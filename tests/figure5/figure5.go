package main

import (
	"fmt"
)

func main() {
	for i := 17; i <= 21; i++ {
		go func() {
			apiVersion := fmt.Sprintf("v1.%d", i)
			_ = apiVersion
		}()
	}
}
