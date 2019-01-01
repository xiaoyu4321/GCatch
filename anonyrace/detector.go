package anonyrace

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/ssa"
	"strings"
)

type lockChanTuple struct {
	name string
	status bool //true for lock, false for unlock,true for send, false for receive
	inst string
}

// Record LOAD/STORE instructions refer to shared var
type SharedVarReferrer struct {
	LoadInsts []*ssa.UnOp
	StoreInsts []*ssa.Store
}

func (svr SharedVarReferrer) String() string {
	var formatStr string
	formatStr += fmt.Sprintf("Load: %v\t", svr.LoadInsts)
	formatStr += fmt.Sprintf("Store: %v", svr.StoreInsts)
	return formatStr
}

// Record AnonFunc and CallerFunc referrers of the shared var
type ResultInfo struct {
    goroutine string
}

type Results map[*ssa.FreeVar] ResultInfo
var unbufferedChan = make(map[string] bool)
/*
func (results Results) String() string {

	var formatStr string

	for freeVar, resultInfo := range results {
		formatStr += fmt.Sprintf("AnonVar: %v\n\tAnonFunc: %v\n\tAnonReferrer: %v\nCallerVar: %v\n\tCallerFunc: %v\n\tCallerReferrer: %v\n",
			freeVar, resultInfo.AnonFunc, resultInfo.AnonReferrer, resultInfo.CallerVar, resultInfo.CallerFunc, resultInfo.CallerReferrer)
	}

	return formatStr
}
*/
func isLock(callCommon *ssa.CallCommon) bool {
	if checkLock(callCommon, "(*sync.Mutex).Lock") ||
		checkLock(callCommon, "(*sync.RWMutex).RLock") ||
		checkLock(callCommon, "(*sync.RWMutex).Lock") {
		return true
	}
	callStr := strings.ToLower(callCommon.String())
	if strings.Contains(callStr, ".lock") ||
		strings.Contains(callStr, ".rlock"){
		return true
	}
	return false
}

func isUnLock(callCommon *ssa.CallCommon) bool {
	if checkLock(callCommon, "(*sync.Mutex).UnLock") ||
		checkLock(callCommon, "(*sync.RWMutex).RUnLock") ||
		checkLock(callCommon, "(*sync.RWMutex).UnLock") {
		return true
	}
	callStr := strings.ToLower(callCommon.String())
	if strings.Contains(callStr, ".unlock") ||
		strings.Contains(callStr, ".runlock"){
		return true
	}
	return false
}

func checkLock(call *ssa.CallCommon, name string) bool{
	if call.IsInvoke() {
		return false
	}
	switch v := call.Value.(type) {
	case *ssa.Function:
		fn, ok := v.Object().(*types.Func)
		if !ok {
			return false
		}
		return fn.FullName() == name
	case *ssa.Builtin:
		return v.Name() == name
	}
	return false
}


// Note: I cannot find a way to get ALL the functions by traversing pkg.Members
// because member functions are missed. Only public functions are listed.
// I have to find all the Call instructions to get the inner functions, maybe some
// functions are still missed.
// TODO: bring up a better method to get All the functions
func GetMemFuncs(callerFunc *ssa.Function) []*ssa.Function {
	memFuncs := make([]*ssa.Function, 0)

	fmt.Println("func1: ", callerFunc.Params)
	for _, BB := range callerFunc.Blocks {
		for _, II := range BB.Instrs {
			switch II.(type) {
			case *ssa.Call:
				if callInst, ok := II.(*ssa.Call); ok {
					callValue := callInst.Common().Value
					if funcValue, ok := callValue.(*ssa.Function); ok {
						memFuncs = append(memFuncs, funcValue)
					}
				}
			}
		}
	}

	return memFuncs
}

func getName(current string) string{
	start := strings.Index(current, ".")
	end := strings.Index(current, "[")
	return current[start+1: end-1]
}
func getUnbufferedChan(caller *ssa.Function){
	for _, BB := range caller.Blocks {
		for j, II := range BB.Instrs {
			switch (II).(type) {
			case *ssa.MakeChan:
				if (II).(*ssa.MakeChan).Size.String() == "0:int" {
					var name string
					if _, ok := BB.Instrs[j-1].(*ssa.FieldAddr); !ok {
						create := BB.Instrs[j-1].String()
						start := strings.Index(create, "(")
						end := strings.Index(create, ")")
						name = create[start+1:end]
						/*if strings.Contains(II.Parent().Name(), "$") {
							name = II.Parent().Parent().Name() + " " + create[start+1:end]
						} else {
							name = II.Parent().Name() + " " + create[start+1:end]
						}*/
						unbufferedChan[name] = true
					}else {
						chanName := getName(BB.Instrs[j-1].String())
						//for k := j - 2; k >= 0; k -- {
						//	if id := BB.Instrs[k].String(); id == expr.X.String() {
							//	start := strings.Index(id, "(")
							//	end := strings.Index(id, ")")
								//name = id[start+1:end] + " " + chanName
								name = BB.Instrs[j-1].(*ssa.FieldAddr).X.Type().String() + " " + chanName
								unbufferedChan[name] = true
								break
							//}
						//}
					}
				}
			case *ssa.Call:
				if callInst, ok := II.(*ssa.Call); ok {
					callValue := callInst.Common().Value
					if funcValue, ok := callValue.(*ssa.Function); ok {
						getUnbufferedChan(funcValue)
					}
				}
			case *ssa.Go:
				if fn, ok := ((II).(*ssa.Go).Call.Value).(*ssa.Function); ok {
					getUnbufferedChan(fn)
				}
			}
		}
		}
	}

func getLockChanList(instrs []ssa.Instruction, id string) []lockChanTuple {
	var list []lockChanTuple
	var name string
	var deferBuffer []int
	for j, instr := range instrs {
	//	fmt.Println("inst:", instr)
		if _, ok := instr.(*ssa.Defer); ok {
			deferBuffer = append(deferBuffer, j)
		}
		if _, ok := instr.(*ssa.RunDefers); ok {
			for i := len(deferBuffer)-1; i >= 0 ; i -- {
				j = deferBuffer[i]
				instr = instrs[j]
				call, ok := instr.(*ssa.Defer)
				if !ok {
					continue
				}
				if isLock(call.Common()) {
					_, ok := instrs[j-3].(*ssa.FieldAddr)
					if !ok {
						name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					}else {
						n := instrs[j-4].(*ssa.DebugRef).X.Type().String()
						name = n + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					}
					lock := lockChanTuple{name, true, instr.String()}
					list = append(list, lock)
					continue
				}
				if isUnLock(call.Common()) {
					_, ok := instrs[j-3].(*ssa.FieldAddr)
					if !ok {
						name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					}else {
						n := instrs[j-4].(*ssa.DebugRef).Expr.(*ast.Ident).String()
						name = n + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					}
					lock := lockChanTuple{name, false, instr.String()}
					list = append(list, lock)
					continue
				}

				callValue := call.Common().Value
				if funcValue, ok := callValue.(*ssa.Function); ok {
					for _, BB := range funcValue.Blocks {
						expr := instrs[j-1].(*ssa.DebugRef).Expr
						list = append(list, getLockChanList(BB.Instrs, expr.(*ast.Ident).String())...)
					}
				}
				if call.Common().IsInvoke() {
					fmt.Println(call.Common().Value.Type())
				}
				if _, ok := callValue.(*ssa.Builtin); ok {
					if strings.Contains(call.Common().String(), "close") {
						if _, ok := instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident); ok {
							name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
						}else{
							n := instrs[j-5].(*ssa.DebugRef).X.Type().String()
							name = n + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
						}
						if unbufferedChan[name] {
							chann := lockChanTuple{name, false, instr.String()}
							list = append(list, chann)
						}
					}
				}
			}
			break
		}
		// add channel send and receive to the list
		switch (instr).(type) {
/*		case *ssa.Alloc:
			if strings.Contains(instr.String(), "*") {
				local = instrs[j+3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
		// instruction is ch <- 1
		case *ssa.Send:
			_, ok := instrs[j-1].(*ssa.DebugRef).Expr.(*ast.SelectorExpr)
			if !ok {
				name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
			/*	if strings.Contains(instr.Parent().Name(), "$") {
					name = instr.Parent().Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}else{
					name = instr.Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
			}else {
				n := instrs[j-5].(*ssa.DebugRef).X.Type().String()
				name = n + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				/*n := instrs[j-5].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				if n != local {
					name = n + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				} else {
					name = id + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
			}
			if unbufferedChan[name] {
				chann := lockChanTuple{name, false, instr.String()}
				list = append(list, chann)
			}

			//instruction is <- ch
		case *ssa.UnOp:
			if (instr).(*ssa.UnOp).Op == token.ARROW {
				_, ok := instrs[j-1].(*ssa.DebugRef).Expr.(*ast.SelectorExpr)
				if !ok {
					name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				/*	if strings.Contains(instr.Parent().Name(), "$") {
					name = instr.Parent().Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}else{
					name = instr.Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
				}else {
					n := instrs[j-5].(*ssa.DebugRef).X.Type().String()
					name = n + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					/*n := instrs[j-5].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					if n != local {
						name = n + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					} else {
						name = id + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					}*/
				}
				if unbufferedChan[name] {
					chann := lockChanTuple{name, false, instr.String()}
					list = append(list, chann)
				}
			}
		case *ssa.Select:
			se := (instr).(*ssa.Select).States
			idx := j
			for i:=0;i<len(se);i++ {
				if _, ok := instrs[idx-1].(*ssa.DebugRef).Expr.(*ast.SelectorExpr); ok {
					name = instrs[idx-5].(*ssa.DebugRef).X.Type().String() + " " + instrs[idx-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					idx = j-5
				}else{
					name = instrs[idx-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
					idx = j-2
				}
				if unbufferedChan[name] {
					chann := lockChanTuple{name, false, instr.String()}
					list = append(list, chann)
				}
			}
		}
		//add locks to the list
		call, ok := instr.(*ssa.Call)
		if !ok {
			continue
		}
		if isLock(call.Common()) {
			_, ok := instrs[j-3].(*ssa.FieldAddr)
			if !ok {
				name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
			/*	if (strings.Contains(instr.Parent().Name(), "$")) {
					name = instr.Parent().Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}else{
					name = instr.Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
			}else {
				n := instrs[j-4].(*ssa.DebugRef).X.Type().String()
				name = n + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
			/*	if n != local {
					name = n + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				} else {
					name = id + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
			}
			lock := lockChanTuple{name, true, instr.String()}
			list = append(list, lock)
			continue
		}
		if isUnLock(call.Common()) {
			_, ok := instrs[j-3].(*ssa.FieldAddr)
			if !ok {
				name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
			/*	if (strings.Contains(instr.Parent().Name(), "$")) {
					name = instr.Parent().Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}else{
					name = instr.Parent().Name() + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
			}else {
				n := instrs[j-4].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				name = n + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
			/*	if n != local {
					name = n + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				} else {
					name = id + " " + instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}*/
			}
			lock := lockChanTuple{name, false, instr.String()}
			list = append(list, lock)
			continue
		}

		callValue := call.Common().Value
		if funcValue, ok := callValue.(*ssa.Function); ok {
			for _, BB := range funcValue.Blocks {
				expr := instrs[j-1].(*ssa.DebugRef).Expr
				list = append(list, getLockChanList(BB.Instrs, expr.(*ast.Ident).String())...)
			}
		}
		if call.Common().IsInvoke() {
			fmt.Println(call.Common().Value.Type())
		}
		if _, ok := callValue.(*ssa.Builtin); ok {
			if strings.Contains(call.Common().String(), "close") {
				if _, ok := instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident); ok {
					name = instrs[j-1].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}else{
					n := instrs[j-5].(*ssa.DebugRef).X.Type().String()
					name = n + " " + instrs[j-3].(*ssa.DebugRef).Expr.(*ast.Ident).String()
				}
				if unbufferedChan[name] {
					chann := lockChanTuple{name, false, instr.String()}
					list = append(list, chann)
				}
			}
		}
	}
	return list
}
func getMemGoFuncs(callerFunc *ssa.Function) map[string] []lockChanTuple {
	list := make(map[string] []lockChanTuple)
	for _, BB := range callerFunc.Blocks {
		for _, II := range BB.Instrs {
			switch II.(type) {
			case *ssa.Call:
				if callInst, ok := II.(*ssa.Call); ok {
					callValue := callInst.Common().Value
					if funcValue, ok := callValue.(*ssa.Function); ok {
						getMemGoFuncs(funcValue)
					}
				}
			case *ssa.Go:
				if fn, ok := ((II).(*ssa.Go).Call.Value).(*ssa.Function); ok {
					for _, BBS := range fn.Blocks {
				//		list[fn.String()] = append(list[fn.String()],getLockChanList(BBS.Instrs, BB.Instrs[i-1].(*ssa.DebugRef).Expr.(*ast.Ident).String())...)
						list[fn.String()] = append(list[fn.String()],getLockChanList(BBS.Instrs, "")...)
					}
				}
				if fn, ok := (II).(*ssa.Go).Call.Value.(*ssa.MakeClosure);ok {
					for _, BBS := range fn.Fn.(*ssa.Function).Blocks {
						list[fn.String()] = append(list[fn.String()],getLockChanList(BBS.Instrs, "")...)
					}
			}
			}
		}
	}

	return list
}

func CheckCallerFunc(callerFunc *ssa.Function) []Results {

	var results []Results
	var list = make(map[string] []lockChanTuple)
    getUnbufferedChan(callerFunc)
	fmt.Println("unbuffer: ", unbufferedChan)
//get list for main function
    for _, BB := range callerFunc.Blocks {
		list[callerFunc.String()] = append(list[callerFunc.String()], getLockChanList(BB.Instrs, "")...)
	}
    temp := list
	fmt.Println("list: ", list)
	//get list for goroutine function
	list = getMemGoFuncs(callerFunc)
	fmt.Println("golist: ", list)
	for k, v := range temp {
		list[k] = v
	}

	stack := make(map[string] bool)
	lockList := make(map[string] bool)
	lockChan := make(map[string] ResultInfo)
    for fn, LL := range list {
    	for _, ele := range LL {
    		if strings.Contains(ele.inst, "Mutex") {
				// if there is a lock in the map, pop out that lock
				if stack[ele.name] && !ele.status {
					delete(stack, ele.name)
					continue
				}
				if !stack[ele.name] && ele.status{
					stack[ele.name] = true
					continue
				}
				continue
			}
    		for lock, _ := range stack {
    			res := ResultInfo{goroutine:fn}
    			lockChan[lock+ele.name] = res
			}
		}

	}
    if len(lockChan) == 0 {
    	fmt.Println("no lock channel bug")
	}
//fmt.Println("lockchan: ", lockChan)
    for fn, LL := range list{
		for _, ele := range LL {
			if strings.Contains(ele.inst, "Mutex") {
				if ele.status {
					lockList[ele.name] = true
				}
				continue
			}
			for lock, _ := range lockList {
				if i, ok := lockChan[lock+ele.name]; ok && i.goroutine != fn {
					fmt.Println("bug: ", fn, i.goroutine)
				}
			}
		}
	}

	return results
}


// First get package-level function list
func Check(mainPkg *ssa.Package) {
	var funcList []*ssa.Function

	for name, member := range mainPkg.Members {
		switch f := member.(type) {
		case *ssa.Function:
			if name == "init" {
				break
			}

			funcList = append(funcList, f)
		}
	}

	for _, funcVar := range funcList {

		results := CheckCallerFunc(funcVar)
		for _, result := range results {
			fmt.Println(result)
		}
	}

}


func tryParseMakeChan(inst *ssa.Instruction) *ssa.MakeChan {
	switch (*inst).(type) {
	case *ssa.MakeChan:
		makeChan := (*inst).(*ssa.MakeChan)
		return makeChan
	}
	return nil
}
func tryParseGo(inst *ssa.Instruction) *ssa.Go {
	switch (*inst).(type) {
	case *ssa.Go:
		instGo := (*inst).(*ssa.Go)
		return instGo
	}
	return nil
}