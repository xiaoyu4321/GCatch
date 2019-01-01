package ssabuilder

import (
	"fmt"
	"reflect"
	"strconv"

	"golang.org/x/tools/go/ssa"
)

func GetMainPkg(prog *ssa.Program) *ssa.Package {
	pkgs := prog.AllPackages()

	for _, pkg := range pkgs {
		if pkg.Pkg.Name() == "main" {
			return pkg 
		}
	}

	return nil
}

func PrintCFG(f * ssa.Function) {

	for _, bb := range f.Blocks {
		fmt.Print(strconv.Itoa(bb.Index))
		fmt.Print(" -> ")
		for _, sbb := range bb.Succs {
			fmt.Print(strconv.Itoa(sbb.Index))
			fmt.Print(" ")
		}
		fmt.Println()	
	}
}

func PrintBB(BB * ssa.BasicBlock) {

	var wValue ssa.Value
	var rValue ssa.Value

	for _, II := range BB.Instrs {
	
		switch inst := II.(type) {
		case *ssa.DebugRef:
			//break
		case *ssa.Alloc:
			fmt.Printf("Alloc %s\n", inst.String())
		case *ssa.Store:
			switch addr := inst.Addr.(type) {
			case *ssa.IndexAddr:
				//fmt.Printf("%s %s %s %s\n", reflect.TypeOf(addr.X), addr.X.Name(), reflect.TypeOf(addr.Index), addr.Index.Name(),)
				wValue = addr.X
			}

			fmt.Printf("Store %s\n", inst.String())
			fmt.Printf("%s %s\n", reflect.TypeOf(inst.Addr), inst.Addr.Name())
			fmt.Println(reflect.TypeOf(inst.Val))
			fmt.Println("====================")
		case *ssa.Call:
			switch arg := inst.Call.Args[0].(type) {
				case *ssa.Slice:
					
					if arg.Low == arg.High && arg.High == arg.Max && arg.Low == nil {
						rValue = arg.X;
					}


					
			}


			fmt.Printf("Call %s %s\n", inst.Call.String(), reflect.TypeOf(inst.Call.Args[0]))
		}
	}


	fmt.Println(wValue)
	fmt.Println(rValue)

	if wValue == rValue {
		fmt.Println("equal")
	}


	//		for _, II := range bb.Instrs {
	//		//fmt.Println(II)
	//		//fmt.Println(reflect.TypeOf(II))
	//		switch inst := II.(type) {
	//		case *ssa.Store:
	//			fmt.Println(inst.Addr)
	//			//fmt.Println(inst.Val)
	//			switch v := inst.Val.(type) {
	//			case *ssa.MakeInterface:
	//				fmt.Println(v.X)
	//			}
	//		}
	//	}	
}
