section \<open>Definition and Comparison of Voting Models\<close>

theory Voting_Models
  imports "HOL-Algebra.Bij"

begin

subsection \<open>Voting Models\<close>

text \<open>
  A voting model is a formalization of a voting system.
  Any voting model, one way or another, should model the collective decision carried out through
  a voting model via its...
    - eligible voters \<V>
    - decisions/ballots \<B> that the voters decide upon
    - potential election outcomes \<O>
    - representation \<M> of the decision process itself
    - tallying method that, based on the decision procedure and
        valid decisions in \<B> made by all voters \<V>, yield an election outcome \<O>
    - specific mechanisms for manipulating and interpreting the model

  Note that a specific tallying method is just one interpretation of a voting model's components.
  There may be other sensible interpretations of the same or similar structures. For instance,
  a simple voting game may be interpreted as binary decision between 2 alternatives with a single
  winner, or with potentially tied winners. 
  As another instance, the decision process may be 
  described in arbitrary detail by letting the voters choose both public and private options
  while the tallying method still considers only the public choices.
\<close> 

record ('v, 'b, 'o, 'x) mechanisms =
  has_swing_vote :: "'x \<Rightarrow> 'v \<Rightarrow> bool"
  rename_model :: "('v \<Rightarrow> 'v) \<Rightarrow> 'x \<Rightarrow> 'x"

locale voting_model =
  fixes 
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "'x" and
      (* 
        \<M> is the mathematical structure representing the decision process.
        It may contain details that are ultimately irrelevant to the tallying method.
      *)
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" and
      (* Intuitively, f describes the core of \<M> as a decision process. *)
    mech :: "('v, 'b, 'o, 'x) mechanisms" (structure)
  assumes
    valid_outcomes: "\<forall> p::'v \<Rightarrow> 'b. p ` \<V> \<subseteq> \<B> \<longrightarrow> f p \<in> \<O>"

subsection \<open>Comparison of Voting Models\<close>

text \<open>
  For two voting models with different descriptions \<M>, \<M>' of the decision process
  to be isomorphic, the voters, ballots, outcomes and tallying method necessarily need to be equal.
  Further requirements about isomorphism of \<M>, \<M>' can be added.
\<close>
(* 
  TODO too strict, require only a bijection between the voter sets?  
*)
locale model_isomorphism = 
  m1: voting_model \<V> \<B> \<O> \<M> f mech + m2: voting_model \<V> \<B>' \<O>' \<M>' f' mech'
  for 
    \<V> :: "'v set" and
    \<B> :: "'b set" and \<B>' :: "'c set" and
    \<O> :: "'o set" and \<O>' :: "'u set" and
    \<M> :: "'x" and \<M>' :: "'y" and
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" and f' :: "('v \<Rightarrow> 'c) \<Rightarrow> 'u" and
    mech :: "('v, 'b, 'o, 'x) mechanisms" and 
    mech' :: "('v, 'c, 'u, 'y) mechanisms"  +
  fixes 
    iso :: "'x \<Rightarrow> 'y \<Rightarrow> bool"
  assumes
    iso: "iso \<M> \<M>'" and
    bij_transform: 
      "\<exists> \<pi> \<phi>. bij \<pi> \<and> bij_betw \<pi> \<B> \<B>' \<and> bij_betw \<phi> \<O> \<O>' \<and> 
        (\<forall> p q. \<phi> (f p) = f' (\<lambda> v. \<pi> (p v)) \<and> 
        f' q = \<phi> (f (\<lambda> v. (the_inv \<pi>) (q v))))" and
    equiv_swing: "\<forall> v \<in> \<V>. has_swing_vote mech \<M> v \<longleftrightarrow> has_swing_vote mech' \<M>' v"

locale model_set_isomorphism =
  fixes \<V> :: "'v set" and 
    \<B> :: "'b set" and \<O> :: "'o set" and \<B>' :: "'c set" and \<O>' :: "'u set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and \<M>' :: "('y \<times> (('v \<Rightarrow> 'c) \<Rightarrow> 'u)) set" and
    iso :: "'x \<Rightarrow> 'y \<Rightarrow> bool" and mech :: "('v, 'b, 'o, 'x) mechanisms" and 
    mech' :: "('v, 'c, 'u, 'y) mechanisms"
  assumes
    correspondence\<^sub>r: (* implies being a voting_model *)
      "\<forall> (m, f) \<in> \<M>. \<exists> m' f'. (m', f') \<in> \<M>' \<and> 
        model_isomorphism \<V> \<B> \<B>' \<O> \<O>' m m' f f' mech mech' iso" and
    correspondence\<^sub>l: (* implies being a voting_model *)
      "\<forall> (m', f') \<in> \<M>'. \<exists> m f. (m, f) \<in> \<M> \<and> 
        model_isomorphism \<V> \<B> \<B>' \<O> \<O>' m m' f f' mech mech' iso" and
    occurrence:
      "\<forall> m::'x. \<forall> m'::'y. \<forall>f f'. 
        model_isomorphism \<V> \<B> \<B>' \<O> \<O>' m m' f f' mech mech' iso \<longrightarrow> 
          ((m,f) \<in> \<M> \<longleftrightarrow> (m',f') \<in> \<M>')" and
    equiv_rename: 
      "\<forall> \<pi> \<in> Bij \<V>. \<forall> m::'x. \<forall> m'::'y. \<forall>f f'. (m, f) \<in> \<M> \<longrightarrow> 
        model_isomorphism \<V> \<B> \<B>' \<O> \<O>' m m' f f' mech mech' iso \<longrightarrow>
          (\<exists> g g'. (rename_model mech \<pi> m, g) \<in> \<M> \<and> (rename_model mech' \<pi> m', g') \<in> \<M>' \<and>
            model_isomorphism 
              \<V> \<B> \<B>' \<O> \<O>' (rename_model mech \<pi> m) (rename_model mech' \<pi> m') g g' mech mech' iso)"

subsection \<open>Exemplary Instantiations\<close>

text \<open> 
  Any voting model is isomorphic to itself if decision processes 
  are required to be identical in order to be isomorphic.
\<close>
lemma self_isomorphism:
  fixes
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "'x" and
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" and
    mech :: "('v, 'b, 'o, 'x) mechanisms"
  assumes
    "voting_model \<V> \<B> \<O> f"
  shows
    "model_isomorphism \<V> \<B> \<B> \<O> \<O> \<M> \<M> f f mech mech (\<lambda>x y. x = y)"
proof (unfold_locales, simp_all)
  show "\<forall>p. p ` \<V> \<subseteq> \<B> \<longrightarrow> f p \<in> \<O>"
    using assms
    unfolding voting_model_def
    by blast
next
  have "bij id"
    by simp
  moreover have "bij_betw id \<B> \<B>"
    by simp
  moreover have "\<forall>p. id (f p) = f (\<lambda>v. id (p v))"
    by simp
  moreover have "(\<forall>q. f q = id (f (\<lambda>v. the_inv id (q v))))"
    unfolding the_inv_into_def
    by simp
  ultimately show "\<exists>\<pi>. bij \<pi> \<and> bij_betw \<pi> \<B> \<B> \<and> (\<exists>\<phi>. bij_betw \<phi> \<O> \<O> \<and> 
    (\<forall>p. \<phi> (f p) = f (\<lambda>v. \<pi> (p v))) \<and> (\<forall>q. f q = \<phi> (f (\<lambda>v. the_inv \<pi> (q v)))))"
    by blast
qed

end