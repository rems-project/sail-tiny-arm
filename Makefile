MODEL=prelude.sail simple-arm-defs.sail simple-arm.sail  interface.sail
OUT_NAME=simpl

default: coq

$(OUT_NAME)_types.v $(OUT_NAME).v: $(MODEL)
	sail -coq -o $(OUT_NAME) $(MODEL)

%.vo: %.v
	coqc $<

$(OUT_NAME).vo: $(OUT_NAME)_types.vo

coq: $(OUT_NAME).vo

interactive:
	sail -i $(MODEL)

clean:
	rm -f $(OUT_NAME)_types.v $(OUT_NAME).v
	rm -f $(OUT_NAME)_types.vo $(OUT_NAME).vo
	rm -f $(OUT_NAME)_types.vok $(OUT_NAME).vok
	rm -f $(OUT_NAME)_types.vos $(OUT_NAME).vos
	rm -f $(OUT_NAME)_types.glob $(OUT_NAME).glob
	rm -f .$(OUT_NAME)_types.aux .$(OUT_NAME).aux

.PHONY: clean coq default interactive
