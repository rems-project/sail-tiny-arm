MODEL=$(shell cat sail_files)
# Those 2 are picked up by dune, hence the export
export SAIL_OPTS=--strict-var
export SAIL_ROCQ_OPTS=--rocq-record-update

default: rocq

rocq:
	dune build

rocq-snapshot:
	@# First build the file and then check that they match
	-dune build @snapshot --auto-promote
	@dune build @snapshot

check:
	sail $(SAIL_OPTS) --just-check $(MODEL)

interactive:
	sail $(SAIL_OPTS) -i $(MODEL)

clean:
	dune clean

.PHONY: clean rocq rocq-snapshot check default interactive

lean:
	mkdir -p lean-snapshot
	sail --lean-force-output --lean-output-dir lean-snapshot --lean -o SailTinyArmUser $(MODEL)
