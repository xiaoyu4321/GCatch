package ssabuilder

import (
	"fmt"
	"go/build"
	"golang.org/x/tools/go/loader"

	"go/parser"
	"go/token"
	//"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"io"
	"io/ioutil"
	"log"
)


type Config struct {
	Files [] string
	Source string 
	BuildLog io.Writer
	PtaLog io.Writer
	LogFlags int
	BadPkgs map[string] string
}

type SSAInfo struct {
	BuildConf * Config
	IgnoredPkgs [] string
	FSet * token.FileSet
	Prog * ssa.Program
	PtaConf * pointer.Config
	Logger * log.Logger
}

var (
	// Packages that should not be loaded (and reasons) by default
	badPkgs = map[string]string{
		"fmt":     "Recursiv calls unrelated to communication",
		"reflect": "Reflection not supported for static analyser",
		"runtime": "Runtime contains threads that are not user related",
		"strings": "Strings function does not have communication",
		"sync":    "Atomics confuse analyser",
		"time":    "Time not supported",
		"rand":    "Math does not use channels",
	}
)

func NewConfig(files []string) (*Config, error) {

	if len(files) == 0 {
		return nil, fmt.Errorf("no files specifed to analyze")
	}

	return & Config {
		Files: files,
		BuildLog: ioutil.Discard,
		PtaLog: ioutil.Discard,
		LogFlags: log.LstdFlags,
		BadPkgs: badPkgs,
	}, nil
}

func (conf * Config) Build() (*SSAInfo, error) {

	// TODO: I have tried to test all the build config here, but not work or work but no difference

	//it is possible to set this one as ad hoc package
	//var lconf = loader.Config{Build: &build.Default}

	// Change build and parser mode
	myBuild := build.Default
	//myBuild.CgoEnabled = true
	//myBuild.UseAllFiles = false
	//fmt.Println(build.Default)
	//fmt.Println(myBuild)

	var lconf = loader.Config{ParserMode: parser.AllErrors, Build: &myBuild}
	//var lconf = loader.Config{ParserMode: parser.DeclarationErrors, Build: &myBuild}
	//var lconf = loader.Config{ParserMode: parser.ImportsOnly, Build: &myBuild}
	//var lconf = loader.Config{ParserMode: parser.PackageClauseOnly, Build: &myBuild}
	//fmt.Println("###lconf.ParserMode: ", lconf.ParserMode)
	// End of change

	buildLog := log.New(conf.BuildLog, "ssabuild: ", conf.LogFlags)

	args, err := lconf.FromArgs(conf.Files, false)

	if err != nil {
		return nil, err
	}

	if len(args) > 0 {
		return nil, fmt.Errorf("surplus arguments: %q", args)
	}

	lprog, err := lconf.Load()

	if err != nil {
		return nil, err
	}

	//prog := ssautil.CreateProgram(lprog, ssa.GlobalDebug|ssa.BareInits)
	prog := ssautil.CreateProgram(lprog, ssa.GlobalDebug|ssa.NaiveForm|ssa.BuildSerially)

	ptaConf, err := setupPTA(prog, lprog, conf.PtaLog)

	ignoredPkgs := []string{}

	if len(conf.BadPkgs) == 0 {
		prog.Build()
	} else {
		for _, info := range lprog.AllPackages {
			if reason, badPkg := conf.BadPkgs[info.Pkg.Name()]; badPkg {
				buildLog.Printf("Skip package: %s (%s)", info.Pkg.Name(), reason)
				ignoredPkgs = append(ignoredPkgs, info.Pkg.Name() )
			} else {
				//prog.Package(info.Pkg).SetDebugMode(true)
				prog.Package(info.Pkg).Build()
			}
		}
	}

	return &SSAInfo{
		BuildConf: conf,
		IgnoredPkgs: ignoredPkgs,
		FSet: lprog.Fset,
		Prog: prog,
		PtaConf: ptaConf,
		Logger: buildLog,
	}, nil
}