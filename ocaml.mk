INCLUDES:=
DEPEND:=.depend
ALL_ML:=$(shell find . -name '*.ml')
ALL_MLI:=$(shell find . -name '*.mli')
OCAMLOPTFLAGS=$(INCLUDES)

default: subst.cmx

%.cmi: %.mli
	ocamlopt $(OCAMLOPTFLAGS) -c $<

%.cmx: %.ml
	ocamlopt $(OCAMLOPTFLAGS) -c $<

$(DEPEND): $(ALL_MLI) $(ALL_ML)
	ocamldep $(INCLUDES) $^ > $@

include $(DEPEND)
