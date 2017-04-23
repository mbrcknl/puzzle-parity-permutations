(*  Title:      HOL/Library/LaTeXsugar.thy
    Author:     Gerwin Klein, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(* Extracted from the Isabelle distribution, version 2016-1, which contains
   the following copyright notice, license and disclaimer. *)

(*
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2016,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

theory LaTeX_Rule_Sugar
imports Main
begin

(* THEOREMS *)
notation (Rule output)
  Pure.imp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>\\mbox{}\\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms"
  ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\\\\\<close>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

notation (Axiom output)
  "Trueprop"  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{}}{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

notation (IfThen output)
  Pure.imp  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
syntax (IfThen output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close> /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

notation (IfThenNoBox output)
  Pure.imp  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
syntax (IfThenNoBox output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")

end
