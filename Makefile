ifdef DEBUG
OCAMLC = ocamlc -g
SUF = .cmo
else 
ifdef PROF
OCAMLC = ocamlcp
SUF = .cmo
else 
OCAMLC = ocamlopt
SUF = .cmx
endif
endif
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc

MODULES = var op ctx util \
	  absyn parser lexer tcabsyn \
	  il ilsubst tcil lift optimize translate \
          lfpl simplify tclfpl lfpl2il\
	  ltal ltalsubst eval tcltal codegen stackcodegen
INTERFACES = util var op ctx \
	  absyn parser tcabsyn \
	  il ilsubst tcil lift optimize translate \
          lfpl simplify tclfpl lfpl2il\
	  ltal ltalsubst eval tcltal codegen stackcodegen
SRCS = $(addsuffix .ml, $(MODULES))
OBJS = $(addsuffix $(SUF), $(MODULES))
ISRCS = $(addsuffix .mli, $(INTERFACES))
IOBJS = $(addsuffix .cmi, $(INTERFACES))
GEN = parser.ml parser.mli lexer.ml

all : lstalc ltalc $(IOBJS) $(OBJS)

ltalc: $(IOBJS) $(OBJS) toplevel$(SUF)
	$(OCAMLC) $(OBJS) toplevel$(SUF) -o $@
lstalc: $(IOBJS) $(OBJS) stacktoplevel$(SUF)
	$(OCAMLC) $(OBJS) stacktoplevel$(SUF) -o $@


%.cmi : %.mli
	$(OCAMLC) -c $< -o $@

%$(SUF) : %.ml
	$(OCAMLC) -c $< -o $@

lexer.ml: lexer.mll
	$(OCAMLLEX) lexer.mll

parser.mli: parser.mly
	$(OCAMLYACC) parser.mly

parser.ml: parser.mli

include .depend


depend : 
	$(OCAMLDEP) toplevel.ml stacktoplevel.ml $(ISRCS) $(SRCS) > .depend

clean : 
	rm -rf *.cmi *.o *.dump *.cmo *.cmx *~ $(GEN) ltalc lstalc


