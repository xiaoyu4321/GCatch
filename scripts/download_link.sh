#!/usr/bin/env bash
# Download new repo
# usage: ./download_link.sh github.com/aaa/bbb
# must be exec under the current dir
# make sure GCatch in the upper dir

MYPROJECT=$1
go get -u $MYPROJECT/...; ln -s $GOPATH/src/$MYPROJECT ../tests/

./extract_pkg.py ../tests/$(basename -- "$MYPROJECT")

echo "start GCatch..."
cd ..
./GCatch > result
echo "end GCatch!"

echo "start reading..."
cd scripts/
./read_result.py ../result
echo "end reading!"
