## HowTo
Regenerate Makefile:
```sh
$ coq_makefile -f _CoqProject -o Makefile
```
or
```sh
$ make Makefile.conf
```

clean project:
```sh
$ make clean
```

build file:
```sh
$ make ${FILE_NAME}.vo
```
