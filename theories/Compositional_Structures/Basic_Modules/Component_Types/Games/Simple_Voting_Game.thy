section \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Cooperative_Game

begin

subsection \<open>Simple Voting Games\<close>

type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set \<Rightarrow> bool)"

fun SVG_payoff :: "'v Simple_Voting_Game \<Rightarrow> ('v set \<Rightarrow> real)" where
  "SVG_payoff G S = (if (snd G S) then 1 else 0)"

fun players :: "'v Simple_Voting_Game \<Rightarrow> 'v set" where
  "players G = fst G"

fun value_fun :: "'v Simple_Voting_Game \<Rightarrow> ('v set \<Rightarrow> bool)" where
  "value_fun G = snd G"

type_synonym 'v SVG_Voting_Power_Domain = "'v Simple_Voting_Game \<times> 'v"

fun game :: "'v SVG_Voting_Power_Domain \<Rightarrow> 'v Simple_Voting_Game" where
  "game G = fst G"

fun player :: "'v SVG_Voting_Power_Domain \<Rightarrow> 'v" where
  "player G = snd G"

fun uncurry2 :: "('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry2 f = (\<lambda>(x,y). f x y)"

type_synonym 'v SVG_Voting_Power = "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> real"

subsection \<open>Classical Voting Power Indices\<close>

(* TODO *)

subsection \<open>Voting Power Axioms on Simple Voting Games\<close>

type_synonym 'v SVG_Voting_Power_Axiom = 
  "'v SVG_Voting_Power \<Rightarrow> 'v SVG_Voting_Power_Domain set \<Rightarrow> bool"

fun np :: "'v SVG_Voting_Power_Domain \<Rightarrow> bool" where
  "np G = True" (* TODO: player G is in no minimal winning coalition in game G *)

fun null_player :: "'v SVG_Voting_Power_Axiom" where
  "null_player \<delta> \<G> = (\<forall> G \<in> \<G>. np G \<longrightarrow> uncurry2 \<delta> G = 0)" (* TODO *)

end