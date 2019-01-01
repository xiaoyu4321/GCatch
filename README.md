# GCatch

concurrency bug detector for Go

## Install

1. ```go get github.com/songlh/GCatch```
2. ```cd ${GOPATH}/src/github.com/songlh/GCatch```
3. ```go build```

## Demo

1. ```cd scripts/```
2. ```./extract_pkg.py ../tests/anonyrace1/```
3. ```cd ..```
4. ```./GCatch```

## Usage

1. ```cd scripts/```
2. ```./download_link.sh github.com/aaa/bbb```


## Output

```
###pkgName: ../tests/anonyrace1/:main
###filePaths: [tests/anonyrace1/anonyrace1.go]
###start checking...
AnonVar: freevar i : *int
	AnonFunc: main.main$1
	AnonReferrer: Load: [*i]	Store: []
CallerVar: new int (i)
	CallerFunc: main.main
	CallerReferrer: Load: [*t2 *t2]	Store: [*t2 = t5]
```

Note: the scenario of ```main.test``` can **NOT** be checked because NO STORE after Go instruction in CallerFunc!

Tested on Ubuntu 16.04, go version go1.9.1 linux/amd64
