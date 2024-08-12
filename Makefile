MODEL=prelude.sail simple-arm-defs.sail simple-arm.sail interface.sail
OUT_NAME=simple
SAIL_OPTS=--strict-var

default: coq

$(OUT_NAME)_types.v $(OUT_NAME).v: $(MODEL)
	sail $(SAIL_OPTS) --coq -o $(OUT_NAME) $(MODEL)

%.vo: %.v
	coqc $<

$(OUT_NAME).vo: $(OUT_NAME)_types.vo

coq: $(OUT_NAME).vo

check:
	sail $(SAIL_OPTS) --just-check $(MODEL)

interactive:
	sail $(SAIL_OPTS) -i $(MODEL)

clean:
	rm -f $(OUT_NAME)_types.v $(OUT_NAME).v
	rm -f $(OUT_NAME)_types.vo $(OUT_NAME).vo
	rm -f $(OUT_NAME)_types.vok $(OUT_NAME).vok
	rm -f $(OUT_NAME)_types.vos $(OUT_NAME).vos
	rm -f $(OUT_NAME)_types.glob $(OUT_NAME).glob
	rm -f .$(OUT_NAME)_types.aux .$(OUT_NAME).aux

.PHONY: clean coq check default interactive
