package ssabuilder

import (
	"fmt"
	"io"

	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
)

func setupPTA(prog * ssa.Program, lprog * loader.Program, ptaLog io.Writer) (*pointer.Config, error) {

	var testPkgs, mains [] * ssa.Package
	for _, info := range lprog.InitialPackages() {

		initialPkg := prog.Package(info.Pkg)

		if initialPkg.Func("main") != nil {
			mains = append(mains, initialPkg)
		} else {
			testPkgs = append(testPkgs, initialPkg)
		}
	}

	if testPkgs != nil {

		for _, testPkg := range testPkgs {

			if p := prog.CreateTestMainPackage(testPkg); p != nil {
				mains = append(mains, p)
			}
		}
	}

	if mains == nil {
		return nil, fmt.Errorf("analysis scope has no main and no tests")
	}

	return &pointer.Config{
		Log: ptaLog,
		Mains: mains,
		Reflection: false,
	}, nil
}