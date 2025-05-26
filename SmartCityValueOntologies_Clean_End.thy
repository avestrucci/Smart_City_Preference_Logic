theory SmartCityValueOntologies_Clean_End (*\<copyright> A. Vestrucci 2025*)
  imports Main
begin
nitpick_params[user_axioms,expect=genuine,show_all,format=3]
declare[[show_types]]
(*  We model three value ontologies for Smart City projects, using a modal preference logic 
  with ceteris paribus (all else equal) operators (after van Benthem et al., 2009). 
  Each ontology defines how project outcomes (sets of promoted values) are compared.*)

(*datatype Cluster = A | B | C
fun cluster_of :: "Value \<Rightarrow> Cluster" where
  "cluster_of A1 = A" | "cluster_of A2 = A" | "cluster_of A3 = A" |
  "cluster_of B1 = B" | "cluster_of B2 = B" | "cluster_of B3 = B" |
  "cluster_of C1 = C" | "cluster_of C2 = C" | "cluster_of C3 = C"*)

typedecl p   (* projects*)
typedecl w   (*possible worlds; in our encoding, these correpond to possible Smart Cities*)

datatype Value = A1 | A2 | A3 | B1 | B2 | B3 | C1 | C2 | C3
type_synonym cluster = "Value set"

definition cluster_A :: cluster where
  "cluster_A = {A1, A2, A3}"

definition cluster_B :: cluster where
  "cluster_B = {B1, B2, B3}"

definition cluster_C :: cluster where
  "cluster_C = {C1, C2, C3}"

abbreviation A where "A \<equiv> cluster_A"
abbreviation B where "B \<equiv> cluster_B"
abbreviation C where "C \<equiv> cluster_C"

definition cluster_of :: "Value \<Rightarrow> Value set" where
  "cluster_of \<equiv> \<lambda> v . (if v \<in> A then A
                   else if v \<in> B then B
                   else C)"
lemma "A \<equiv> cluster_of A1" 
  by (simp add: cluster_A_def cluster_of_def)  (*trivial test*)

consts promotes :: "p \<Rightarrow> Value " (*NB: "promotes" returns a single value.*)
consts promotes_pred :: "p \<Rightarrow> Value \<Rightarrow> bool" (*now "promotes" returns a set of values*)
consts promotes_set :: "p \<Rightarrow> Value set" (*Idem*)

text \<open>We impose that every project promotes at least one value:\<close>
axiomatization where (*promotes_in_set: "promotes P \<in> promotes_set P" and*)
  set_nonempty:    "\<forall> P. promotes_set P \<noteq> {}"

(*(* Each Smart City project  has an incidence relation I indicating which values it promotes. *)
consts I :: "  p \<Rightarrow> Value \<Rightarrow> bool"   (* I p v means that project p  promotes value v *)
abbreviation Iset :: "  p \<Rightarrow> Value set" where
  "Iset p \<equiv> {v. v = promotes p }"   (* The set of values promoted in project p *)*)


(********************************************************************************************************************)
text \<open>Ontology_Fix: A fixed value order.

Ontology 1 does not need modal logic, because there are no alternatives to quantify over. Of course the projects 
can be different - i.e. they can promote different values - but, regardless of the values they promote, 
their preference is fixed by the fixed value ranking. Hence, there are no alternatives, thus  no need for modal logic. 
Of course, the section on ceteris paribus (CP) makes use of the modal encoding by Benzm\"uller at al, by treating 
 projects as possible worlds. \<close>

locale Ontology_Fix
begin

definition cluster_rank :: "cluster \<Rightarrow> nat" where (*fixed ranking of clusters*)
  "cluster_rank X =
(if X = A then 3 else if X = B then 2 else 1)"

(*Alternative ranking: 

fun v_rank :: "Value \<Rightarrow> nat"  where                
  "v_rank A1 = 9" | "v_rank A2 = 8" | "v_rank A3 = 7" |
  "v_rank B1 = 6" | "v_rank B2 = 5" | "v_rank B3 = 4" |
  "v_rank C1 = 3" | "v_rank C2 = 2" | "v_rank C3 = 1"

The following definitions are remade below, for ceteris paribus:
abbreviation best_rank :: "p \<Rightarrow> nat"  where
  "best_rank P \<equiv> Max (v_rank ` Iset P)"      (* well-defined because Max works on finite sets*)
definition best_val :: "p \<Rightarrow> Value" where
  "best_val P \<equiv> (THE v. v \<in> Iset P \<and> v_rank v = best_rank P)"
*)

fun intra_rank :: "Value \<Rightarrow> nat" where
  "intra_rank A1 = 3" | "intra_rank A2 = 2" | "intra_rank A3 = 1" |
  "intra_rank B1 = 3" | "intra_rank B2 = 2" | "intra_rank B3 = 1" |
  "intra_rank C1 = 3" | "intra_rank C2 = 2" | "intra_rank C3 = 1"

definition vGreater :: "Value \<Rightarrow> Value \<Rightarrow> bool"  (infix "\<succ>v" 50) where (*ordering of values in Ontology 1, reflecting 
the fixed ranking of clusters*)
  "v \<succ>v w  \<equiv>
     (cluster_rank (cluster_of v) > cluster_rank (cluster_of w)) \<or>
     (cluster_of v = cluster_of w \<and> intra_rank v > intra_rank w)"

(*Tests:*)
lemma "A1 \<succ>v A2 " 
  by (simp add: cluster_A_def cluster_of_def vGreater_def)
lemma "C1 \<succ>v A1"  oops (*ctm, as expected*)
lemma "A3 \<succ>v B3"    unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by auto
lemma "A1 \<succ>v C1" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by auto
lemma "C1 \<succ>v A1" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def oops (*ctm*)
lemma "B1 \<succ>v B1" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def oops (*ctm*)
lemma "\<forall> v. A1 \<noteq> v \<longrightarrow> A1  \<succ>v v" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by auto

text \<open>Preference relation between Smart City projects. This preference is based on the value ordering: 
if a project X promotes a value higher than the value promoted by the project Y, then X is preferable to Y.\<close>

definition pBetter :: "p \<Rightarrow> p \<Rightarrow> bool" (infix "\<succeq>p" 50) where
  "P \<succeq>p Q  \<equiv>   (promotes P = promotes Q) \<or> (promotes P \<succ>v promotes Q) " 
(*betterness relation between projects: also reflexive, because two projects can be ranked the same. 
This gives S4 frame*)

(*Tests*)
lemma   " \<forall> P Q. (promotes P \<succ>v promotes Q )  \<longrightarrow> (P \<succeq>p Q)" 
  by (simp add: pBetter_def) (*trivial: tested connection b. values ranking and projects betterness*)
lemma pTrans:  "P \<succeq>p Q \<Longrightarrow> Q \<succeq>p R \<Longrightarrow> P \<succeq>p R" 
  unfolding pBetter_def vGreater_def  by fastforce

(*Tests with concrete values:*)
lemma "\<forall> P Q. (( A1 = promotes P) \<and> (B3 = promotes Q)) \<longrightarrow> (P \<succeq>p Q)" 
  unfolding pBetter_def vGreater_def vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by simp
lemma "\<forall> P Q. (( B2 = promotes P) \<and> (C1 = promotes Q)) \<longrightarrow> (P \<succeq>p Q)" 
 unfolding pBetter_def vGreater_def vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def  by auto
lemma "\<forall> P Q. (( B2 = promotes P) \<and> (C1 = promotes Q)) \<longrightarrow> (Q \<succeq>p P)"
  nitpick (*ctm as expected*) oops
lemma "\<forall> P Q. (( A1 = promotes P) \<and> (A1 = promotes Q)) \<longrightarrow> (P \<succeq>p Q)"
 unfolding pBetter_def vGreater_def vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by simp

(*We define a second betterness relation for projects promoting clusters; this is based on ranking of clusters:*)
abbreviation Iset :: "p \<Rightarrow> cluster" where
  "Iset p \<equiv> cluster_of (promotes p)"
definition clGreater :: "Value set \<Rightarrow> Value set \<Rightarrow> bool"  (infix "\<succ>cl" 50) where 
  "v \<succ>cl w  \<equiv>  (cluster_rank v > cluster_rank w)"
definition pBetter2 :: "p \<Rightarrow> p \<Rightarrow> bool" (infix "\<succeq>p2" 50) where 
  "P \<succeq>p2 Q  \<equiv>   (Iset P = Iset Q) \<or> (Iset P \<succ>cl Iset Q) " 

(*Tests:*)
lemma "\<forall> P Q. (( B = Iset P) \<and> (C = Iset Q)) \<longrightarrow> (P \<succeq>p2 Q)" 
  unfolding pBetter_def vGreater_def  cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def clGreater_def pBetter2_def   by auto
lemma "\<forall> P Q. (( C = Iset P) \<and> (A = Iset Q)) \<longrightarrow> (P \<succeq>p2 Q)" 
  nitpick (*ctm as expected*) oops
lemma exists_best_cluster_project:
  assumes "\<exists>P. \<forall>Q. Iset P \<succ>cl Iset Q"
  shows   "\<exists>P. \<forall>Q. P \<succeq>p2 Q"   using assms clGreater_def by auto

text \<open>A project can promote multiple values: in this case, it is enough to know the top value for each project 
in order to know which is the best project in a comparison: in this case, the other values are considered equivalent. 
This is a Ceteris paribus situation interpreted as epistemic negative (e.g. "I am not concerned by what I do not know"). 
First, we need to introduce third version of the betterness relation between projects, because we need
to establish that, in case a project promotes a set of values, the betterness is defined on the 
highest ranked value in the set of values that the project promotes.\<close>

definition best_val :: "p \<Rightarrow> Value" where
  "best_val P \<equiv> (SOME v. v \<in> promotes_set P \<and> (\<forall> w \<in> promotes_set P. intra_rank v \<le> intra_rank w))"

(*lemma best_val_in_set: "best_val P \<in> promotes_set P"
  unfolding best_val_def using set_nonempty sledgehammer

lemma best_val_min: "w \<in> promotes_set P \<Longrightarrow> intra_rank (best_val P) \<le> intra_rank w"
  unfolding best_val_def using set_nonempty
  by (rule someI2_ex)  (auto intro: Min_le)*)

definition pBetter3  :: "p \<Rightarrow> p \<Rightarrow> bool" (infix "\<succeq>p3" 50) where
  "P \<succeq>p3 Q  \<equiv>  intra_rank (best_val P) \<le> intra_rank (best_val Q)"
definition Iset2 :: "p \<Rightarrow> Value set" where "Iset2 P \<equiv> { v. v \<in> promotes_set P }"

(*Here below the ceteris paribus is introduced: for every variable in \<Gamma>, P and Q give the same truth value. 
In our semantics this corresponds to say that whenever the value is in \<Gamma>, either both projects promote it
 or neither does.*)
definition cp_projects ("_\<^bold>\<equiv>\<^sub>__") where "P \<^bold>\<equiv>\<^sub>\<Gamma> Q \<equiv> \<forall>v. v \<in> \<Gamma> \<longrightarrow> (v \<in> Iset2 P \<longleftrightarrow> v \<in> Iset2 Q)"
definition cp_projects_better ("_\<^bold>\<unrhd>\<^sub>__") where "P \<^bold>\<unrhd>\<^sub>\<Gamma> Q \<equiv> ( P \<succeq>p3 Q) \<and> (P \<^bold>\<equiv>\<^sub>\<Gamma> Q)"
lemma "P = Q \<longrightarrow> P \<^bold>\<unrhd>\<^sub>\<Gamma> Q " (*confirmed reflexive*) 
  by (simp add: cp_projects_better_def cp_projects_def pBetter3_def)

lemma
  assumes "A1 \<in> Iset2 P"    and "A1 \<notin> \<Gamma>"
  and "\<forall> Q. \<not> A1 \<in> Iset2 Q" and "B1 \<notin> \<Gamma>"
      and "P \<^bold>\<equiv>\<^sub>\<Gamma> Q"
(*      and "\<forall>v. v \<in> Iset2 Q \<and> v \<notin> \<Gamma> \<longrightarrow> A1 \<succ>v v"*) (*no need to assume that A1 outreaches all other values.*)
and NonEmpty:  "\<exists>v. v \<in> Iset2 Q \<and> v \<notin> \<Gamma>"
and \<Gamma>NonEmpty : "\<exists> w. w \<in>  \<Gamma>"
  shows   "P \<^bold>\<unrhd>\<^sub>\<Gamma> Q" 
  using assms(1) assms(3) by auto
 
(*definition projset_preferred :: "Value set \<Rightarrow> Value set \<Rightarrow> bool" where
  "projset_preferred S T \<equiv> (\<exists> v \<in> S. \<forall> u \<in> T. rank v > rank u)"
definition project_preferred :: " p \<Rightarrow>  p \<Rightarrow> bool" where
  "project_preferred w1 w2 \<equiv> projset_preferred (Iset w1) (Iset w2)"

(* In this ontology, one project is preferred over another if the highest-ranked value it promotes 
   is ranked higher than the highest value promoted by the other. *)
lemma pref_higher_value:
  assumes "\<exists> v \<in> Iset w1. \<forall> u \<in> Iset w2. rank v > rank u"
  shows "project_preferred w1 w2"
  using assms project_preferred_def projset_preferred_def by auto*)

end

(********************************************************************************************************************)

text  \<open>In Ontology_Flex things are different: The preference between projects varies because 
it is parametrized by conditions e.g. needed values  (a smart city wants to promote specific values and 
select the projects accordingly). This requires the introduction of a possible worlds semantics, 
where, in the context of our application, the possible worlds are interpreted as possible smart cities.\<close>

locale Ontology_Flex =
  fixes  raw_SCV :: "w \<Rightarrow> Value set" (* Raw value set parametric on worlds *) and
         raw_NV  :: "Value set"  (*Raw set of needed values, according to specific requirements/guidelines/policies. 
                                  Not parametric on worlds because it is assumed to hold everywhere*) and
         Smart_City_Values :: "w \<Rightarrow> Value set" and
         NeededVals :: "Value set" (*These last two constants are used for the following theory-specific definitions:*)
        defines SCV_def:   "Smart_City_Values w \<equiv> raw_SCV w \<inter> (A \<union> B \<union> C)" (*Specification of the value set for this theory*)
         and NV_def:   "NeededVals \<equiv> raw_NV \<inter> (A \<union> B \<union> C)" (*Specification of the needed values for this theory*)
begin

(*Test (trivial): both are subset*)
lemma subset_SCV: "Smart_City_Values w \<subseteq> (A \<union> B \<union> C)" 
  unfolding SCV_def by auto
lemma subset_NV:  "NeededVals \<subseteq> (A \<union> B \<union> C)"
  unfolding NV_def by auto

(*We define the "smart values" in a world as the intersection of the values in this world with the needed values:*)
definition smart_values :: "w \<Rightarrow> Value set" where (* values in a possible world (AKA possible Smart City) that meet the needed values*)
  "smart_values w = Smart_City_Values w \<inter> NeededVals"

(*Based on this, we define the weak betterness relation between worlds AKA possible Smart Cities: 
a smart city X is better than smart city Y if Y's values that meet the needed values are a subset of X's values 
that meet the needed values:*)
definition better_world :: "w \<Rightarrow> w \<Rightarrow> bool"  (infix "\<succeq>\<^sup>w" 50) where 
  "w \<succeq>\<^sup>w v \<equiv> smart_values v \<subseteq> smart_values w" 

(*Tests (trivial): we have S4*)
lemma refl: "w \<succeq>\<^sup>w w"  by (simp add: better_world_def)
lemma trans: "w \<succeq>\<^sup>w v \<Longrightarrow> v \<succeq>\<^sup>w u \<Longrightarrow> w \<succeq>\<^sup>w u"  unfolding better_world_def by (meson order.trans)
lemma  "(w \<succeq>\<^sup>w v) \<and> (v \<succeq>\<^sup>w w)" nitpick oops (*ctm expected*)
lemma "w \<succeq>\<^sup>w v \<Longrightarrow> v \<succeq>\<^sup>w w \<Longrightarrow> smart_values w = smart_values v" 
  using better_world_def by auto (*antisymmetric up to extensional equality of the value sets*)

(*We also define the strong variant - irreflexive:*)
definition better_strict_world :: "w \<Rightarrow> w \<Rightarrow> bool"  (infix "\<succ>\<^sup>w" 60) where 
  "w \<succ>\<^sup>w v \<equiv> w \<succeq>\<^sup>w v \<and> \<not> v \<succeq>\<^sup>w w"   

end

(*Now we run some tests, in a sublocale:*)

locale Two_Worlds_Test = Ontology_Flex +
  fixes W V :: w
  assumes raw_NV_def: "raw_NV = {A1, A3, B2, B3, C1, C3}"
      and raw_SCV_W:  "raw_SCV W = {A1, A3, B1, B3}"
      and raw_SCV_V:  "raw_SCV V = {A1, A2, B1, C2}"
begin

lemma smart_W: "smart_values W = {A1, A3, B3}"
using raw_NV_def raw_SCV_W
  unfolding smart_values_def SCV_def NV_def
            cluster_A_def cluster_B_def cluster_C_def   by auto

lemma smart_V: "smart_values V = {A1}"
using raw_NV_def raw_SCV_V
  unfolding  smart_values_def  SCV_def  NV_def 
  cluster_A_def cluster_B_def cluster_C_def   by simp

lemma W_better_V:  " W \<succeq>\<^sup>w V"
  using smart_W smart_V
  unfolding smart_values_def SCV_def NV_def better_world_def       by simp

end

(*In Ontology_Card I introduce a variant of the betterness relation between worlds that is based on cardinality.
 Now a world X is better than Y iff the cardinality of the intersection between X's values and the needed values 
is greater than the cardinality of the values of Y  with the needed values:*)

locale Ontology_Card = Ontology_Flex + Two_Worlds_Test
begin

definition better_card :: "w \<Rightarrow> w \<Rightarrow> bool"  (infix "\<succeq>\<^sup>c" 50) where 
  "w \<succeq>\<^sup>c v \<equiv> (card (smart_values w)) \<ge> (card (smart_values v))"

definition better_card_strong :: "w \<Rightarrow> w \<Rightarrow> bool"  (infix "\<succ>\<^sup>c" 60) where
  "w \<succ>\<^sup>c v \<equiv> card (smart_values w) > card (smart_values v)"

(*Basic algebric tests: weak is a pre-order, strong is an irreflexive & transitive order*)
lemma card_refl: "w \<succeq>\<^sup>c w" 
  by (simp add: better_card_def)
lemma card_trans:  "w \<succeq>\<^sup>c v \<Longrightarrow> v \<succeq>\<^sup>c u \<Longrightarrow> w \<succeq>\<^sup>c u"
  by (meson better_card_def le_trans)
lemma strict_imp_weak:  "w \<succ>\<^sup>c v \<Longrightarrow> w \<succeq>\<^sup>c v" 
  by (simp add: better_card_def better_card_strong_def)
lemma strong_card_irrefl: "\<not> w \<succ>\<^sup>c w"
  by (simp add: better_card_strong_def)
lemma strict_trans:   "w \<succ>\<^sup>c v \<Longrightarrow> v \<succ>\<^sup>c u \<Longrightarrow> w \<succ>\<^sup>c u" 
  using better_card_strong_def order.strict_trans by blast

(*We evoke the previous concrete cases, W and V:*)
lemma smart_W_card: "card (smart_values W) = 3"
  unfolding smart_values_def SCV_def NV_def
            raw_NV_def raw_SCV_W
            cluster_A_def cluster_B_def cluster_C_def   
  using raw_NV_def smart_W by fastforce

lemma smart_V_card: "card (smart_values V) = 1"
  using smart_V by simp

lemma W_strictly_better_V_q: "W \<succ>\<^sup>c V"
  unfolding better_card_strong_def smart_W_card smart_V_card try  by simp

end



text \<open>The previous locales Ontology_Flex and Ontology_Card were needed to reason about projects. 
Indeed, the fact that a specific world (or set of worlds) has some values means that there is a project in that world 
(AKA Smart City) that promotes these values. Hence, we need now to establish a preference relation for the projects.
This time, the preference between projects is based not on a value  ranking (like in Ontology_Fix), 
but on the order between worlds: the project preference is the order lifted to possible worlds. 
In other words  the order is applied to world-lifted propositions: the project preference is hence encoded as 
\<lambda>-expressions (higher-order functions) parametized on worlds (elements of type w). Informally, this means that
  a project is preferred to another one iff the Smart Cities that implement this projects  are better than
 the Smart Cities that implement the other project.
I introduce two preference relations, one based on the subset version,
 and another one based on the cardinality version:*) \<close>


locale Preference_Projects = Ontology_Flex + Two_Worlds_Test + Ontology_Card

begin

(*preference between projects, based on the subset version, with all quantifier permutations:*)
abbreviation preferenceEA :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>E\<^sup>A" 45)
 where "\<phi> \<succeq>\<^sup>E\<^sup>A \<psi> \<equiv>  \<lambda> w. \<exists> u. \<phi> u \<and> (\<forall> v. \<psi> v \<longrightarrow> u \<succeq>\<^sup>w v)"
abbreviation preferenceEE :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>E\<^sup>E" 45)
 where "\<phi> \<succeq>\<^sup>E\<^sup>E \<psi> \<equiv>  \<lambda> w. \<exists> u. \<phi> u \<and> (\<exists> v. \<psi> v \<and> u \<succeq>\<^sup>w v)"
abbreviation preferenceAE :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>A\<^sup>E" 45)
 where "\<phi> \<succeq>\<^sup>A\<^sup>E \<psi> \<equiv>  \<lambda> w. \<forall> u. \<phi> u \<longrightarrow> (\<exists> v. \<psi> v \<and> u \<succeq>\<^sup>w v)"
abbreviation preferenceAA :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>A\<^sup>A" 45)
 where "\<phi> \<succeq>\<^sup>A\<^sup>A \<psi> \<equiv>  \<lambda> w. \<forall> u. \<phi> u \<longrightarrow> (\<forall> v. \<psi> v \<longrightarrow> u \<succeq>\<^sup>w v)"

(*We make the tests with concrete projects:*)

lemma P_pref_Q :
  fixes  P Q :: "w \<Rightarrow> bool"
  assumes NV:   "NeededVals = {A1, A3, C3}"
      and svP:  "\<And>w. P w \<Longrightarrow> Smart_City_Values w = {A1, A3, B3, C3}"
      and svQ:  "\<And>w. Q w \<Longrightarrow> Smart_City_Values w = {A3, C3, B2}"
      and P_ex: "\<exists>w. P w"
      and Q_ex: "\<exists>w. Q w"
  shows  "\<forall>w. (P \<succeq>\<^sup>E\<^sup>A Q) w"
proof    
  fix w
  obtain u where Pu: "P u" using P_ex by blast
  have sm_u: "smart_values u = {A1, A3, C3}"  using Pu svP NV
    unfolding smart_values_def SCV_def NV_def by auto
  have sm_v: "\<And>v. Q v \<Longrightarrow> smart_values v = {A3, C3}"  using svQ NV
    unfolding smart_values_def SCV_def NV_def by auto
 have dom: "\<forall>v. Q v \<longrightarrow> u \<succeq>\<^sup>w v" unfolding better_world_def
  using sm_u sm_v by auto
   have "\<exists>u. P u \<and> (\<forall>v. Q v \<longrightarrow> u \<succeq>\<^sup>w v)"   using Pu dom by blast
   thus "(P \<succeq>\<^sup>E\<^sup>A Q) w"   by simp
qed


(*Now the alternative with cardinality, with all quantifier permutations:*)
abbreviation preferenceEA_card :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>E\<^sup>A\<^sub>C" 45)
 where "\<phi> \<succeq>\<^sup>E\<^sup>A\<^sub>C \<psi> \<equiv>  \<lambda> w. \<exists> u. \<phi> u \<and> (\<forall> v. \<psi> v \<longrightarrow> u \<succeq>\<^sup>c v)"
abbreviation preferenceEE_card :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>E\<^sup>E\<^sub>C" 45)
 where "\<phi> \<succeq>\<^sup>E\<^sup>E\<^sub>C \<psi> \<equiv>  \<lambda> w. \<exists> u. \<phi> u \<and> (\<exists> v. \<psi> v \<and> u \<succeq>\<^sup>c v)"
abbreviation preferenceAE_card :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>A\<^sup>E\<^sub>C" 45)
 where "\<phi> \<succeq>\<^sup>A\<^sup>E\<^sub>C \<psi> \<equiv>  \<lambda> w. \<forall> u. \<phi> u \<longrightarrow> (\<exists> v. \<psi> v \<and> u \<succeq>\<^sup>c v)"
abbreviation preferenceAA_card :: "(w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> (w \<Rightarrow> bool)" 
 (infix "\<succeq>\<^sup>A\<^sup>A\<^sub>C" 45)
 where "\<phi> \<succeq>\<^sup>A\<^sup>A\<^sub>C \<psi> \<equiv>  \<lambda> w. \<forall> u. \<phi> u \<longrightarrow> (\<forall> v. \<psi> v \<longrightarrow> u \<succeq>\<^sup>c v)"

(*Test:*)

lemma P_pref_Q_card:
  fixes  P Q :: "w \<Rightarrow> bool"
  assumes NV:   "NeededVals = {A1, A3, C3}"
      and svP:  "\<And>w. P w \<Longrightarrow> Smart_City_Values w = {A1, A3, B3, C3}"
      and svQ:  "\<And>w. Q w \<Longrightarrow> Smart_City_Values w = {A3, C3, B2}"
      and P_ex: "\<exists>w. P w"
      and Q_ex: "\<exists>w. Q w"
  shows  "\<forall>w. (P \<succeq>\<^sup>E\<^sup>A\<^sub>C Q) w"
proof         
  obtain u where Pu: "P u" using P_ex by blast
  have card_u: "card (smart_values u) = 3"   using Pu svP NV
    unfolding smart_values_def SCV_def NV_def   by simp
 have card_v: "\<And>v. Q v \<Longrightarrow> card (smart_values v) = 2"
  using svQ NV unfolding smart_values_def SCV_def NV_def
  by simp
have dom: "\<forall>v. Q v \<longrightarrow> u \<succeq>\<^sup>c v"
  unfolding better_card_def
  using card_u card_v   by simp
  have "\<exists>u. P u \<and> (\<forall>v. Q v \<longrightarrow> u \<succeq>\<^sup>c v)" using Pu dom by blast
  thus "(P \<succeq>\<^sup>E\<^sup>A\<^sub>C Q) w" by simp
qed

end

end

















locale Ontology2 begin

(** Ontology 2: A distinction between intra (within) and iter (amongst)  cluster hierarchy. **)




definition ge_world :: "w \<Rightarrow> w \<Rightarrow> bool" (infix "\<succeq>w" 50) where
  "w \<succeq>w v \<equiv> Smart_City_Values v \<subseteq> Smart_City_Values w"


definition smartVals :: "Value set" where
  "smartVals = A \<union> B \<union> C" 
                  
definition ge_world :: "w \<Rightarrow> w \<Rightarrow> bool"  (infix "\<succeq>\<^sup>w" 60) where
  "w \<succeq>\<^sup>w⪰v \<equiv> smartVals v \<subseteq> smartVals w"   




  fixes cl_greater :: "cluster \<Rightarrow> cluster \<Rightarrow> bool"   (infix "\<succ>\<^sup>c" 50)
  assumes cl_trans: "\<forall> x y z. x  \<succ>\<^sup>c y \<and> y \<succ>\<^sup>c z \<longrightarrow> x \<succ>\<^sup>c z"
and  cl_irrefl: "\<forall>x. \<not>  (x \<succ>\<^sup>c x)"
  and cl_total : "\<forall> x y.  x \<noteq> y \<longrightarrow>  (x \<succ>\<^sup>c y) \<or>  (y \<succ>\<^sup>c x)"

  (* We assume a strict  order on clusters (\<succ>_cl). This allows different 
     priority rankings of the clusters A, B, C (e.g. A \<succ>_cl B \<succ>_cl C, etc.). *)
begin

definition cluster_cw :: "cluster \<Rightarrow> cluster" where
  "cluster_cw X =
     (if X = A then B
      else if X = B then C
      else if X = C then A
      else {})"

fun cluster_cw  :: "cluster \<Rightarrow> cluster " where
  "cluster_cw  A = B" |  "cluster_cw  B = C" |  "cluster_cw  C = A"

definition cluster_ccw :: "cluster \<Rightarrow> cluster" where
  "cluster_ccw x = (THE y. cluster_cw y = x)"

lemma bij_cluster_cw: "bij cluster_cw" 
  by (metis (full_types) Cluster.distinct(1) Cluster.exhaust bij_iff cluster_cw.simps(1) cluster_cw.simps(2) cluster_cw.simps(3))

primrec leader   :: "Cluster \<Rightarrow> Value" where
  "leader A = A1" | "leader B = B1" |  "leader C = C1"

primrec near_cw  :: "Cluster \<Rightarrow> Value" where (*neighbooring values*)
  "near_cw A = A2" |   "near_cw B = B2" |  "near_cw C = C2"

primrec near_ccw :: "Cluster \<Rightarrow> Value" where (*neighbooring values*)
  "near_ccw A = A3" |  "near_ccw B = B3" |   "near_ccw C = C3"

definition intra_lt :: "Value \<Rightarrow> Value \<Rightarrow> bool" where
  "intra_lt x y \<equiv>
     (let C = cluster_of x in
      if C \<noteq> cluster_of y then False
      else if x = leader C then y \<noteq> leader C     
      else if y = leader C then False
      else if cluster_cw C \<succ>\<^sup>c cluster_ccw C
           then x = near_cw C \<and> y = near_ccw C    
           else x = near_ccw  C \<and> y = near_cw C)"

definition outranks :: "Value \<Rightarrow> Value \<Rightarrow> bool"  (infix "\<succ>\<^sup>v" 50) where
  "x \<succ>\<^sup>v y \<equiv>
     (let Cx = cluster_of x; Cy = cluster_of y in
      if Cx \<noteq> Cy then Cx \<succ>\<^sup>c Cy
      else intra_lt x y)"

lemma A_chain:
  assumes order_AB: "A \<succ>\<^sup>c B"
assumes order_BC: "B \<succ>\<^sup>c C" 
shows "leader A \<succ>\<^sup>v  near_cw A" and " near_cw A \<succ>\<^sup>v near_ccw A" 
  apply (simp add: intra_lt_def outranks_def) oops

lemma B_chain:
  assumes order_BA: "B \<succ>\<^sup>c A"
assumes order_AC: "A \<succ>\<^sup>c C" 
shows "leader B \<succ>\<^sup>v  near_ccw B" and " near_ccw B \<succ>\<^sup>v near_cw B" 
  apply (simp add: intra_lt_def outranks_def) oops
 
lemma B_chain:
  assumes order_BA: "B \<succ>\<^sup>c A"
assumes order_AC: "A \<succ>\<^sup>c C" 
shows "leader B \<succ>\<^sup>v  near_cw B" and " near_cw B \<succ>\<^sup>v near_ccw B" 
  nitpick oops (*ctm: expected*)

lemma B_chain_inverted_short:
  assumes  "near_ccw B \<succ>\<^sup>v near_cw B"
  shows    "A \<succ>\<^sup>c C"
  using assms
  unfolding outranks_def intra_lt_def   \<comment> \<open>open the two definitions\<close>
  oops


lemma B_chain_inverted_short:
  assumes  "near_ccw B \<succ>\<^sup>v near_cw B"
  shows    "A \<succ>\<^sup>c C" 
proof -
  have "intra_lt (near_ccw B) (near_cw B)"
    using assms by (simp add: outranks_def)
  \<comment> \<open> last branch of the if-then-else\<close>
  hence "cluster_ccw B \<succ>\<^sup>c cluster_cw B" 
    by (metis Cluster.distinct(1) Cluster.distinct(3) Cluster.distinct(5) Cluster.exhaust Ontology2.intra_lt_def The_unsafe_def Uniq_I Value.distinct(43) Value.distinct(45) Value.distinct(53) cl_total cluster_ccw_def cluster_cw.simps(1) cluster_cw.simps(2) cluster_cw.simps(3) cluster_of.simps(6) intra_lt_def leader.simps(2) near_ccw.simps(2) near_cw.simps(2) the1_equality')
    thus "A \<succ>\<^sup>c C"
       oops



(*definition cluster_cw :: "Cluster \<Rightarrow> Cluster" where 
  "cluster_cw X \<equiv> (case X of A \<Rightarrow> B | B \<Rightarrow> C | C \<Rightarrow> A)"
definition cluster_ccw :: "Cluster \<Rightarrow> Cluster" where 
  "cluster_ccw X \<equiv> (case X of A \<Rightarrow> C | B \<Rightarrow> A | C \<Rightarrow> B)"*)

(*definition intra_lt :: "Value \<Rightarrow> Value \<Rightarrow> bool" where
  "intra_lt x y \<equiv> (
   let C = cluster_of x in
      if C \<noteq> cluster_of y then False    
      else if y = leader C then False
      else if cluster_cw C \<succ>\<^sup>c\<^sup>l cluster_ccw C
           then x = near_ccw C \<and> y = near_cw C  
           else x = near_cw  C \<and> y = near_ccw C)"*)

(*definition outranks :: "Value \<Rightarrow> Value \<Rightarrow> bool" (infix "\<succ>\<^sup>v" 50) where
  " x \<succ>\<^sup>v y \<succ>\<^sup>v z \<equiv>
     ((assume X \<succ>\<^sup>c Y \<succ>\<^sup>c Z) 
      if cluster_of x = X \<and>  cluster_of y = X \<and> cluster_of z = X then 
x = leader X \<and> y 
      else if x = leader C then y \<noteq> leader C     
      else if y = leader C then False
      else if cluster_cw C \<succ>\<^sup>c cluster_ccw C
           then x = near_ccw C \<and> y = near_cw C    
           else x = near_cw  C \<and> y = near_ccw C)"*)




(*Some trivial lemmas:*)
lemma "\<forall> x y.  (x  \<noteq> y \<and>  (x = leader C)) --> (y \<noteq> leader C)" 
  by simp

lemma leader_top: 
"\<forall> x. (cluster_of x = C ) \<longrightarrow> ( leader C \<succ>\<^sup>v x \<or> leader C = x)"
  by (simp add: intra_lt_def outranks_def)
  
lemma intra_asym: "intra_lt a b \<longrightarrow> \<not> intra_lt b a"  oops (*exception?*)
  
lemma outranks_asym: "x \<succ>\<^sup>v y -->  \<not> y \<succ>\<^sup>v x" 
  by (smt (z3) Value.distinct(17) Value.distinct(53) Value.distinct(71) Value.exhaust cl_irrefl cl_trans cluster_of.simps(1) cluster_of.simps(2) cluster_of.simps(3) cluster_of.simps(4) cluster_of.simps(5) cluster_of.simps(6) cluster_of.simps(7) cluster_of.simps(8) cluster_of.simps(9) intra_lt_def leader.simps(2) near_ccw.simps(1) near_ccw.simps(2) near_ccw.simps(3) near_cw.simps(1) near_cw.simps(2) near_cw.simps(3) outranks_def)
 
lemma A3_gt_A2_imp_C_gt_B:
  "(A3 \<succ>\<^sup>v A2) \<longrightarrow> (B \<succ>\<^sup>c C)" oops

lemma both_directions_hold:
  shows "A3 \<succ>\<^sup>v A2 \<Longrightarrow> B \<succ>\<^sup>c C"
    and "A3 \<succ>\<^sup>v A2 \<Longrightarrow> C \<succ>\<^sup>c B" oops (*ctm*)

lemma only_one_direction_holds:
   "(A2 \<succ>\<^sup>v A3) \<longrightarrow> (B \<succ>\<^sup>c C)" oops (*no ctm but no proof either*)

lemma only_one_inverted_direction_holds:
   "(B \<succ>\<^sup>c C) \<longrightarrow> (A2 \<succ>\<^sup>v A3) " oops (*no ctm but no proof*)

lemma A3_gt_A2_implies_unique_outer:
  assumes "A3 \<succ>\<^sup>v A2"
  shows   "C \<succ>\<^sup>c B" unfolding "intra_lt_def" and "outranks_def" oops (*no ctm but no proof*)


(*  We induce an intra-cluster value order based on 
   the cluster priority: if the clockwise neighboring cluster is ranked higher (X_clockwise \<succ>_cl X_counterclockwise), 
   then the value leaning toward that higher neighbor (X2) is preferred to the one leaning toward the lower neighbor (X3), ceteris paribus. 
   X1 is always the top value within cluster X. *)
(*definition outranks :: "Value \<Rightarrow> Value \<Rightarrow> bool" (infix "\<succ>" 50) where 
  "x \<succ> y \<equiv> (
     let A = cluster_of x; B = cluster_of y 
     in if A \<noteq> B then A \<succ>_cl B 
        else 
          (if x = (case x of A \<Rightarrow> A1 | B \<Rightarrow> B1 | C \<Rightarrow> C1) then 
              (y \<noteq> (case y of A \<Rightarrow> A1 | B \<Rightarrow> B1 | C \<Rightarrow> C1)) 
           else if y = (case X of A \<Rightarrow> A1 | B \<Rightarrow> B1 | C \<Rightarrow> C1) then False 
          else 
             ((x = (case x of A \<Rightarrow> A2 | B \<Rightarrow> B2 | C \<Rightarrow> C2) \<and> 
               y = (case y of A \<Rightarrow> A3 | B \<Rightarrow> B3 | C \<Rightarrow> C3) \<and> cluster_cw X \<succ>_cl cluster_ccw X)
              \<or> 
              (x = (case X of A \<Rightarrow> A2 | B \<Rightarrow> B2 | C \<Rightarrow> C2) \<and> 
               y = (case X of A \<Rightarrow> A3 | B \<Rightarrow> B3 | C \<Rightarrow> C3) \<and> cluster_cw X \<succ>_cl cluster_ccw X)
              \<or> 
              (x = (case X of A \<Rightarrow> A3 | B \<Rightarrow> B3 | C \<Rightarrow> C3) \<and> 
               y = (case X of A \<Rightarrow> A2 | B \<Rightarrow> B2 | C \<Rightarrow> C2) \<and> \<not>(cluster_cw X \<succ>_cl cluster_ccw X))
             )))"*)

(* Note: The above definition enumerates cases for clarity. 
   - If x and y are from different clusters, x \<succ>₂ y holds iff x’s cluster is ranked above y’s cluster (X \<succ>_cl Y).
   - If x and y are in the same cluster X:
       * If x is the central value X1 (and y is not X1), then x \<succ>₂ y (X1 is top within X). 
       * If y is X1 (and x is not), then x \<prec>₂ y (so x \<succ>₂ y is False).
       * Otherwise, x and y must be X2 and X3. In that case, if cluster_cw X \<succ>_cl cluster_ccw X, then X2 \<succ>₂ X3; 
         if the counterclockwise neighbor cluster is ranked higher (cluster_ccw X \<succ>_cl cluster_cw X), then X3 \<succ>₂ X2. 
   This realizes the “leaning” preference: e.g. if X’s clockwise neighbor cluster is considered more important than the counterclockwise one, 
   the value leaning toward that clockwise side (X2) is preferred over X3 (leaning to the less important side), all else equal.
*)

definition projset_preferred :: "Value set \<Rightarrow> Value set \<Rightarrow> bool" where
  "projset_preferred S T \<equiv> (\<exists> v \<in> S. \<forall> u \<in> T. v \<succ>\<^sup>v u)"

definition project_preferred :: " w \<Rightarrow>  w \<Rightarrow> bool" where
  "project_preferred w1 w2 \<equiv> projset_preferred (Iset w1) (Iset w2)"

(* A project is preferred in this ontology if it includes some value v that outranks all values in the other project (according to the cluster-based value order \<succ>₂). *)
lemma higher_cluster_pref:
  assumes "\<exists> X. (\<exists> v \<in> Iset w1. cluster_of v = X) \<and> (\<forall> u \<in> Iset w2. X \<succ>\<^sup>c cluster_of u)"
  shows "project_preferred w1 w2"
proof -
  from assms obtain X where "\<exists>v \<in> Iset w1. cluster_of v = X" 
                   and H: "\<forall>u \<in> Iset w2. X \<succ>\<^sup>c cluster_of u" by auto
  then obtain v0 where "v0 \<in> Iset w1" and "cluster_of v0 = X" by auto
  hence "\<forall>u \<in> Iset w2. cluster_of v0 \<succ>\<^sup>c cluster_of u" using H by simp
  hence "\<forall>u \<in> Iset w2. v0 \<succ>\<^sup>v u"
    unfolding outranks_def 
    by (metis cl_irrefl) (* cross-cluster case *)
  thus "project_preferred w1 w2"
    unfolding project_preferred_def projset_preferred_def by (meson `v0 \<in> Iset w1`)
qed

(* In particular, if the highest-ranked cluster among w1’s values outranks the highest cluster of w2’s values, then w1 \<succ> w2. 
   (Likewise, if both share the top cluster, the tie is broken by the internal cluster order: 
    e.g. if both promote values from cluster A, a project including A1 (central) is preferred to one whose best is A2 or A3; 
    and if the best values are A2 vs A3, the preference follows the orientation of cluster A’s leanings.) *)
end

(** Ontology 3: Fully flexible (partial value preferences). **)
locale Ontology3 =
  fixes "\<succ>" :: "Value \<Rightarrow> Value \<Rightarrow> bool"   (infix "\<succ>" 50)
  assumes trans_pref: "transitive \<succ>" and irrefl_pref: "irrefl \<succ>"
  (* \<succ> is a strict partial order on values (not assumed total), representing known value preferences. *)
begin

definition projset_preferred :: "Value set \<Rightarrow> Value set \<Rightarrow> bool" where
  "projset_preferred S T \<equiv> (\<exists> v \<in> S. \<forall> u \<in> T. v \<succ> u) \<and> \<not>(\<exists> u \<in> T. \<forall> x \<in> S. u \<succ> x)"
definition project_preferred :: "\<langle>iota\<rangle> \<Rightarrow> \<langle>iota\<rangle> \<Rightarrow> bool" where
  "project_preferred w1 w2 \<equiv> projset_preferred (Iset w1) (Iset w2)"

(* A project w1 is preferred to w2 if w1 promotes at least one value that is known to outrank all values promoted by w2, 
   and w2 does not have any value that outranks all of w1’s values. This ensures a safe (robust) dominance given partial preferences. *)
lemma dominate_preferred:
  assumes "\<exists> v \<in> Iset w1. \<forall> u \<in> Iset w2. v \<succ> u" 
    and "\<not>(\<exists> u \<in> Iset w2. \<forall> x \<in> Iset w1. u \<succ> x)"
  shows "project_preferred w1 w2"
  by (simp add: assms project_preferred_def projset_preferred_def)

(* **Connection to ceteris paribus (CP) modal logic:** 
   We can express such dominance using CP operators:contentReference[oaicite:0]{index=0}:contentReference[oaicite:1]{index=1}. 
   Let \<phi> \<equiv> (\<lambda>w. \<forall>v. (v \<in> Iset w1) \<leftrightarrow> I w v) be a proposition that “world w realizes project w1’s exact values” 
   (similarly for \<psi> and project w2). Let \<Gamma> be the set of all value-formulas on which w1 and w2 do not differ 
   (i.e. values that either both projects promote or both omit). Then under the above assumptions, we obtain a CP preference 
   \<phi> \<prec>\<^sub>A\<^sub>A^\<Gamma> \<psi>: all else being equal (\<Gamma>), any world where w1’s project values hold is strictly preferred 
   to any world where w2’s values hold:contentReference[oaicite:2]{index=2}:contentReference[oaicite:3]{index=3}. In other words, w1’s project *robustly* dominates w2’s project 
   given the known (partial) value order.
*)
end

end
