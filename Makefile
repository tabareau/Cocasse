all: coqcompile

coqcompile:
	coq_makefile -R . "" *.v -o Makefile_coq
	$(MAKE) -f Makefile_coq > /dev/null

clean: 
	$(MAKE) -f Makefile_coq clean
