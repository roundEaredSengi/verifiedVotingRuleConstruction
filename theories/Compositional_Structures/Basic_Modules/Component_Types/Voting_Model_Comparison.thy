section \<open>Voting Model Comparison\<close>

theory Voting_Model_Comparison
  imports "Games/Simple_Voting_Game"
          "Electoral_Module"

begin

subsection \<open>Comparison between Voting Rules and Simple Voting Games\<close>

locale svg_rule_power_comparison = 
  equiv: 
    power_equivalence \<V> \<B> "UNIV::bool set" \<O> "UNIV::bool set" \<M> \<M>' iso \<delta> \<delta>' mech mech'
  for 
    \<V> :: "'v set" and \<B> :: "'b set" and \<O> :: "'o set" and
    \<M> :: "((('v \<Rightarrow> 'b) \<Rightarrow> 'o) \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<M>' :: "('v Simple_Voting_Game \<times> (('v \<Rightarrow> bool) \<Rightarrow> bool)) set" and
    iso :: "(('v \<Rightarrow> 'b) \<Rightarrow> 'o) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" and
    \<delta> :: "('v, ('v \<Rightarrow> 'b) \<Rightarrow> 'o) Voting_Power" and
    \<delta>' :: "('v, 'v Simple_Voting_Game) Voting_Power" and
    mech :: "('v, 'b, 'o, ('v \<Rightarrow> 'b) \<Rightarrow> 'o) mechanisms" and
    mech' :: "('v, bool, bool, 'v Simple_Voting_Game) mechanisms" +
  assumes
    rules: "\<forall> (m, f) \<in> \<M>. voting_rule \<V> \<B> \<O> m" and (* and m = f? *)
    games: "\<forall> (m', f') \<in> \<M>'. simple_voting_game \<V> m'"

interpretation trivial_comparison: svg_rule_power_comparison 
  "{}" "{}" "{default}" "{}" "{}" "\<lambda>r g. True" "\<lambda>r v. 0" "\<lambda>g v. 0" trivial_rule_mech trivial_mech\<^sub>S\<^sub>V\<^sub>G
proof (unfold_locales, simp_all) qed

text \<open>
  Assuming equivalence of \<delta> on voting rules and \<delta>' on simple voting games, 
  they both either satisfy or do not satisfy the null player axiom.
  Thus, equivalence of the null player axiom is necessary for \<delta> and \<delta>' to be equivalent.
\<close>
lemma (in svg_rule_power_comparison) equiv_null_player: 
  "null_player (fst ` \<M>) \<V> (has_swing_vote mech) \<delta> \<longleftrightarrow> 
    null_player (fst ` \<M>') \<V> (has_swing_vote mech') \<delta>'"
proof (simp, safe)
  fix
    V :: "'v set" and
    vf :: "'v set \<Rightarrow> bool" and
    f' :: " ('v \<Rightarrow> bool) \<Rightarrow> bool" and
    v :: 'v
  assume
    valid_game: "((V, vf), f') \<in> \<M>'" and
    voter: "v \<in> \<V>" and
    np: "\<not> has_swing_vote mech' (fst ((V, vf), f')) v" and
    np_ax: "\<forall>m\<in>\<M>. \<forall>v\<in>\<V>. \<not> has_swing_vote mech (fst m) v \<longrightarrow> \<delta> (fst m) v = 0"
  interpret game: simple_voting_game \<V> "(V, vf)" mech'
    using games valid_game
    by blast
  have "\<forall>(m', f')\<in>\<M>'. \<exists>m f. (m, f) \<in> \<M> \<and> 
    model_isomorphism \<V> \<B> UNIV \<O> UNIV m m' f f' mech mech' iso"
    using equiv.moiso.correspondence\<^sub>l 
    by blast
  with valid_game have
    "\<exists> m f. (m, f) \<in> \<M> \<and> model_isomorphism \<V> \<B> UNIV \<O> UNIV m (V, vf) f f' mech mech' iso"
    by blast
  then obtain m :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" and f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o"  where
    valid_rule: "(m, f) \<in> \<M>" and 
    iso: "model_isomorphism \<V> \<B> UNIV \<O> UNIV m (V, vf) f f' mech mech' iso"
    by blast
  hence np': "\<not> has_swing_vote mech (fst (m, f)) v"
    using valid_rule valid_game voter iso np model_isomorphism_def
    by (simp add: model_isomorphism.equiv_swing)
  have "\<delta>' (fst ((V, vf), f')) v = \<delta> (fst (m, f)) v"
    using valid_rule valid_game voter iso equiv.coincide
    by fastforce (* TODO don't use ff *)
  also have "\<delta> (fst (m, f)) v = 0"
    using valid_rule voter np' np_ax
    by blast
  finally show "\<delta>' (fst ((V, vf), f')) v = 0"
    by simp
next
  fix
    r :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" and
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" and
    v :: 'v
  assume
    valid_rule: "(r, f) \<in> \<M>" and
    voter: "v \<in> \<V>" and
    np: "\<not> has_swing_vote mech (fst (r, f)) v" and
    np_ax: "\<forall>m\<in>\<M>'. \<forall>v\<in>\<V>. \<not> has_swing_vote mech' (fst m) v \<longrightarrow> \<delta>' (fst m) v = 0"
  interpret rule: voting_rule \<V> \<B> \<O> r
    using valid_rule rules
    by blast
  have "\<forall>(r, f)\<in>\<M>. \<exists>g f'. (g, f') \<in> \<M>' \<and> 
    model_isomorphism \<V> \<B> UNIV \<O> UNIV r g f f' mech mech' iso"
    using equiv.moiso.correspondence\<^sub>r 
    by blast
  with valid_rule obtain g :: "'v Simple_Voting_Game" and f' :: "('v \<Rightarrow> bool) \<Rightarrow> bool" where
    valid_game: "(g, f') \<in> \<M>'" and 
    iso: "model_isomorphism \<V> \<B> UNIV \<O> UNIV r g f f' mech mech' iso"
    by blast
  hence np': "\<not> has_swing_vote mech' (fst (g, f')) v"
    using valid_rule valid_game voter iso np model_isomorphism_def
    by (simp add: model_isomorphism.equiv_swing)
  have "\<delta> (fst (r, f)) v = \<delta>' (fst (g, f')) v"
    using valid_rule valid_game voter iso equiv.coincide
    by fastforce (* TODO don't use ff *)
  also have "\<delta>' (fst (g, f')) v = 0"
    using valid_game voter np' np_ax
    by blast
  finally show "\<delta> (fst (r, f)) v = 0"
    by simp
qed

end