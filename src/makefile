.PHONY:  compile html

compile:
	make -f CoqMakefile COQLIBS?=''

html:
	make -f CoqMakefile  \
	COQDOCFLAGS?='-g -interpolate -utf8' \
	COQDOC_LIBS?=''  \
	html

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile
