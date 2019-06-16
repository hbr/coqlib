.PHONY:  compile html

compile:
	make -f CoqMakefile

html: compile
	make -f CoqMakefile  \
        COQFLAGS?='-w none' \
	COQDOCFLAGS?='-g -interpolate -utf8 --no-index' \
	COQDOCLIBS?=''  \
	COQLIBS?=''     \
	html

install:
	make -f CoqMakefile install

clean:
	make -f CoqMakefile clean

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile
