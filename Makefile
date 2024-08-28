MODEL=prelude.sail simple-arm-defs.sail simple-arm.sail interface.sail
OUT_NAME=simple
SAIL=sail
SAIL_OPTS=--strict-var
SAIL_COQ_OPTS=--coq-record-update

default: coq

$(OUT_NAME)_types.v $(OUT_NAME).v: $(MODEL)
	$(SAIL) $(SAIL_OPTS) --coq $(SAIL_COQ_OPTS) -o $(OUT_NAME) $(MODEL)

%.vo: %.v
	coqc $<

$(OUT_NAME).vo: $(OUT_NAME)_types.vo

coq: $(OUT_NAME).vo

check:
	$(SAIL) $(SAIL_OPTS) --just-check $(MODEL)

interactive:
	$(SAIL) $(SAIL_OPTS) -i $(MODEL)

clean:
	rm -f $(OUT_NAME)_types.v $(OUT_NAME).v
	rm -f $(OUT_NAME)_types.vo $(OUT_NAME).vo
	rm -f $(OUT_NAME)_types.vok $(OUT_NAME).vok
	rm -f $(OUT_NAME)_types.vos $(OUT_NAME).vos
	rm -f $(OUT_NAME)_types.glob $(OUT_NAME).glob
	rm -f .$(OUT_NAME)_types.aux .$(OUT_NAME).aux

.PHONY: clean coq check default interactive
