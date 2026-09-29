package main

import "syscall"

func main() { syscall.Write(1, []byte("hello world\n")) }
