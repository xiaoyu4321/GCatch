package main

import (
//	"encoding/json"
	"fmt"
	"github.com/songlh/GCatch/anonyrace"
	"github.com/songlh/GCatch/ssabuilder"
	"golang.org/x/tools/go/ssa"
//	"io/ioutil"
	"log"
//	"os"
	"strings"
)

func handlePkgFiles(pkgPathAndName string, filePaths []string) {
	conf, err := ssabuilder.NewConfig(filePaths)
	if err != nil {
		log.Fatal(err)
	}

	ssainfo, err := conf.Build()
	if err != nil {
		//log.Fatal(err)
		return
	}

	var myPkg *ssa.Package

	fields := strings.Split(pkgPathAndName, ":")
	pkgName := fields[1]
	for _, pkg := range ssainfo.Prog.AllPackages() {
		if pkg.Pkg.Name() == pkgName {
			myPkg = pkg
		}
	}

	if myPkg == nil {
		fmt.Println("Fail to find main package")
		return
	}

	fmt.Println("###start checking...")

	// Switch from check and print all
	// TODO: too lazy to write a control option
	anonyrace.Check(myPkg)
	// anonyrace.PrintAll(myPkg)
}

func main() {
/*	jsonFile, err := os.Open("scripts/data.json")
	if err != nil {
		fmt.Println(err)
	}
	defer jsonFile.Close()

	byteValue, _ := ioutil.ReadAll(jsonFile)
	var pkgFiles map[string][]string
	json.Unmarshal([]byte(byteValue), &pkgFiles)
*/
//	for pkgName, filePaths := range pkgFiles {
	pkgName := "tests/figure4/:main"
	filePaths := []string{"tests/figure4/figure4.go"}
		fmt.Println("###pkgName:", pkgName)
		fmt.Println("###filePaths:", filePaths)
		handlePkgFiles(pkgName, filePaths)
//	}
	//pkgName := "grpc"
	//handlePkgFiles(pkgName, pkgFiles[pkgName])
}
