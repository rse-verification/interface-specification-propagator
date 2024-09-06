(lang dune 3.2)
(using dune_site 0.1)
(name frama-c-isp)

(generate_opam_files true)

(license GPL-2.0-or-later)
(maintainers "Gustav Ung")
(authors "The ISP development team")
(source (github rse-verification/isp))
(homepage "https://github.com/rse-verification/interface-specification-propagator")
(version dev)

(package 
  (name frama-c-isp)
 (depends
  (ocaml (>= 4.13.1))
  (frama-c (and (>= 26) (< 29))))
 (synopsis "Automatic inference of ACSL auxilliary annotations")
 (description "This plugin for the Frama-C platform for source code analysis
of C programs provides automatic inference of ACSL auxilliary annotations."))
