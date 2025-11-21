MODEL=$(shell cat sail_files)
# Those 2 are picked up by dune, hence the export
export SAIL_OPTS=--strict-var
export SAIL_COQ_OPTS=--coq-record-update

default: coq

coq:
	dune build

coq-snapshot:
	@# First build the file and then check that they match
	-dune build @snapshot --auto-promote
	@dune build @snapshot

check:
	sail $(SAIL_OPTS) --just-check $(MODEL)

interactive:
	sail $(SAIL_OPTS) -i $(MODEL)

clean:
	dune clean

.PHONY: clean coq coq-snapshot check default interactive

lean:
	-mkdir lean-snapshot
	sail --lean-output-dir lean-snapshot --lean $(MODEL)
