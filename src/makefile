.PHONY:  compile html

compile:
	make -f CoqMakefile COQLIBS?=''

html:
	make -f CoqMakefile  \
	COQDOCFLAGS?='-g -interpolate -utf8 --no-index' \
	COQDOCLIBS?=''  \
	COQLIBS?=''     \
	html

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile
