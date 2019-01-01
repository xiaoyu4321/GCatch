package main

func test() {
	sum := 0

	for j := 0; j < 10; j ++ {
		go func() {
			sum += 1
		}()
	}

	//fmt.Println(sum)
	g(sum)
}

func g(i int) int {
	i++
	return i
}

func main() {

	done := make(chan bool)

	for i := 0; i < 10; i ++ {
//		k := 0
		go func() {
			j := i
//			j := k
			//fmt.Print(j)
			j += 1
			done <- true
		}()
	}

	for i := 0; i < 10; i ++ {
		<- done
	}
}