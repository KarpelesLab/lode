# newlng

New programming language, yet another.

## Goals

* Memory safety by design
* Strong compiler checks
* Impossible to write code that crashes
* Small code should result in small executable (printf("hello world\n"); should end as a write syscall as the printf itself gets optimized out, nothing more)
* No runtime
* As many checks as possible during compile
* Configurable optimization strategies (inlining, etc)
* Able to write low level code, legacy code (8 bits, etc) and kernels
* Exceptions or similar, or at least better error handling than Go
* Parallelism/threads native syntax & elements (that could be coming from a standard library)
* Easy to read and follow
* Enforced formatting (using tabs)
* Multi architecture, multi platform, including wasm
* No asm in the standard library. Syscall calling should be part of the language (somehow)
* Ability to optimize code based on cpu style, including simd/etc, with some hinting possible too (some code may require not to be optimized, such as constant type crypto code)
* Ability for a project to re-implement low level pieces (allocs, syscalls, etc.. maybe by implementing their own os/arch)

## Open questions

### Do we care about calling external libraries?

I think a Go-style approach (native by default, support for ffi via a specific interface, but static builds possible too) is acceptable. Go prove it works, and it helps guarantee safety within the scope of the program.
If we could have a newlng-compiled loadable library support instead, that could be interesting. I know Rust has it but it's mostly unused as it is strongly version dependant.

Loadable libraries are great because code is not duplicated (mmap, shared, etc) and updates are more easily tracked (multiple programs using the same library behind a unified ABI means updating the library updates all the binaries). This has a lot of inconvenients (dll hell, etc). Some opensource licenses were built around this concept (LGPL, OS exception in GPL, etc). Loaded library means no inlining optimizations too, and in some cases (with C/C++) libraries will include some code in their headers (define, etc) meaning that you can end with hybrid and difficult to track cases... so might as well have no loadable binary?
Maybe we can indeed have binaries include a list of compiled in modules and their versions, making it possible to track what a program was compiled with?

### Optimization

We might be working on a firmware for a embedded device with a limited amount of available flash, on a cpu (Cortex-9 or whatever) which may nor may not have a fpu/etc. Or we might be building for a threadripper 9995. Ideally I'd like us to be even able to model cuda environments (lots of cores, lots of registers, very fast memory), or whatever might come our way. If we can find some novel way to do thread synchronization that is even more optimized to what people do nowadays, that's even better.
This also means that inlining/loop unrolling/etc strategy will change a lot depending on what we're targetting.

### Condition stripping

When a condition is guaranteed to be false, we should of course get rid of the code that would have been run. Ideally we should allow the code to be invalid (ie. targetting a different platform, etc) so that people can if (arch==amd64) or whatever that syntax could be.

### string encoding

By default we should of course use utf-8, however I do think we should have the ability to specify a specific string is encoded in a specific encoding. This way we can allow rune iteration on anything. String character types should be defined in the std library, and conversion should not be supported by default (a sjis string will yield sjis runes). Support for conversion will be an extra lib (maybe part of the standard kit).

### no include files

A lot of programming languages have proven that include files are bad, and nowadays we can assume the machine doing the compilation is strong enough to deal with it.

### packaging

I like golang's solution of importing packages by their full git url (github.com/author/project) with the exception of the standard library. This kills typo squatting and ensures people know what they import.


