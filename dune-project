(lang dune 3.8)
(name coq-sail-tiny-arm)
(using coq 0.8)

(source (github rems-project/sail-tiny-arm))
(license "BSD-3-Clause")
(authors
  "Shaked Flur"
  "Brian Campbell"
  "Alasdair Armstrong"
  "Thibaut Pérami"
  "Nils Lauermann"
)
(maintainers "Sail Devs <cl-sail-dev@lists.cam.ac.uk>")
; Arm architecture version followed by a dash and a single incrementing number
(version "9.4-3")

(package
 (name coq-sail-tiny-arm)
 (synopsis " A very simplified and cut down version of the Arm ISA sail specification, handwritten")
 (depends
  (coq (>= 8.15))
  (sail (>= 0.19.1))
  sail_coq_backend
  sail_lem_backend
  sail_c_backend
  sail_lean_backend
  sail_smt_backend
  sail_sv_backend
  sail_ocaml_backend
  sail_latex_backend
  sail_output
  (coq-stdpp (>= 1.10.0))
  (coq-stdpp-bitvector (>= 1.10.0))
  (coq-sail-stdpp (>= 0.18))
  (coq-record-update (>= 0.3.4))
 )
)

(generate_opam_files)
