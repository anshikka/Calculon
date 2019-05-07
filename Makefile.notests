COMPFLAGS = -g -annot
OCC = ocamlc $(COMPFLAGS)
LIBS = 


PROGRAMS = \
	demo_parse \
	demo_eval \
	calculon \

MODULES = \
	calclex.cmo \
	calcparse.cmo \
	calceval.cmo \

TEST_PROGRAMS = \


all : $(MODULES) $(PROGRAMS) 

setup:
	chmod u+x calculon_required_solution
	chmod u+x calculon_optional_solution

calclex.cmo : calclex.ml
	$(OCC) -c $<

calcparse.cmo : calcparse.ml calclex.cmo
	$(OCC) -c $<

demo_parse : calclex.cmo calcparse.cmo demo_parse.ml
	$(OCC) -o $@ $^

calceval.cmo : calceval.ml calcparse.cmo calclex.cmo
	$(OCC) -c $<

demo_eval : calclex.cmo calcparse.cmo calceval.cmo demo_eval.ml
	$(OCC) -o $@ $^

calculon : calclex.cmo calcparse.cmo calceval.cmo calculon.ml
	$(OCC) -o $@ $^

clean :
	rm -f *.cmo *.cmi *.mlt *.annot $(PROGRAMS) $(TEST_PROGRAMS) 

