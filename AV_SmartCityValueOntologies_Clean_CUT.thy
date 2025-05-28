theory AV_SmartCityValueOntologies_Clean_CUT (*© A. Vestrucci 2025*)
  imports Main
begin
nitpick_params[user_axioms,expect=genuine,show_all,format=3]
declare[[show_types]]
(*  We model two value ontologies for Smart City projects, using a modal preference logic 
  with ceteris paribus (all else equal) operators (Benzm\"uller & Fuenmajor after van Benthem et al., 2009). 
  Each ontology defines how project outcomes (sets of promoted values) are compared.*)

(*datatype Cluster = A | B | C
fun cluster_of :: "Value ⇒ Cluster" where
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

abbreviation A where "A ≡ cluster_A"
abbreviation B where "B ≡ cluster_B"
abbreviation C where "C ≡ cluster_C"

definition cluster_of :: "Value ⇒ Value set" where
  "cluster_of ≡ λ v . if v ∈ A then A
                   else if v ∈ B then B
                   else C"
lemma "A ≡ cluster_of A1" 
  by (simp add: cluster_A_def cluster_of_def)  (*trivial test*)


(********************************************************************************************************************)
text ‹Ontology_Fix: A fixed value order.

Ontology 1 does not need modal logic, because there are no alternatives to quantify over. Of course the projects 
can be different - i.e. they can promote different values - but, regardless of the values they promote, 
their preference is fixed by the fixed value ranking. Hence, there are no alternatives, thus  no need for modal logic. 
Of course, the section on ceteris paribus (CP) makes use of the modal encoding by Benzm\"uller at al, by treating 
 projects as possible worlds. ›

locale Ontology_Fix =

fixes promotes :: "p ⇒ Value " (*NB: "promotes" returns a single value.*) and 
 promotes_pred :: "p ⇒ Value ⇒ bool" (*now "promotes" returns a set of values*) and
 promotes_set :: "p ⇒ Value set" (*Idem*) 
 
   assumes (* "promotes P ∈ promotes_set P" and*)  (*We impose that every project promotes at least one value:*)
   "∀ P. promotes_set P ≠ {}"
begin

definition cluster_rank :: "cluster ⇒ nat" where (*fixed ranking of clusters*)
  "cluster_rank X =
(if X = A then 3 else if X = B then 2 else 1)"

(*Alternative ranking: 

fun v_rank :: "Value ⇒ nat"  where                
  "v_rank A1 = 9" | "v_rank A2 = 8" | "v_rank A3 = 7" |
  "v_rank B1 = 6" | "v_rank B2 = 5" | "v_rank B3 = 4" |
  "v_rank C1 = 3" | "v_rank C2 = 2" | "v_rank C3 = 1"

The following definitions are remade below, for ceteris paribus:
abbreviation best_rank :: "p ⇒ nat"  where
  "best_rank P ≡ Max (v_rank ` Iset P)"      (* well-defined because Max works on finite sets*)
definition best_val :: "p ⇒ Value" where
  "best_val P ≡ (THE v. v ∈ Iset P ∧ v_rank v = best_rank P)"
*)

fun intra_rank :: "Value ⇒ nat" where
  "intra_rank A1 = 3" | "intra_rank A2 = 2" | "intra_rank A3 = 1" |
  "intra_rank B1 = 3" | "intra_rank B2 = 2" | "intra_rank B3 = 1" |
  "intra_rank C1 = 3" | "intra_rank C2 = 2" | "intra_rank C3 = 1"

definition vGreater :: "Value ⇒ Value ⇒ bool"  (infix "≻v" 50) where (*ordering of values in Ontology 1, reflecting 
the fixed ranking of clusters*)
  "v ≻v w  ≡
     (cluster_rank (cluster_of v) > cluster_rank (cluster_of w)) ∨
     (cluster_of v = cluster_of w ∧ intra_rank v > intra_rank w)"

(*Tests:*)
lemma "A1 ≻v A2 " 
  by (simp add: cluster_A_def cluster_of_def vGreater_def)
lemma "C1 ≻v A1"  oops (*ctm, as expected*)
lemma "A3 ≻v B3"    unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by auto
lemma "A1 ≻v C1" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by auto
lemma "C1 ≻v A1" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def oops (*ctm*)
lemma "B1 ≻v B1" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def oops (*ctm*)
lemma "∀ v. A1 ≠ v ⟶ A1  ≻v v" unfolding vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by auto

text ‹Preference relation between Smart City projects. This preference is based on the value ordering: 
if a project X promotes a value higher than the value promoted by the project Y, then X is preferable to Y.›

definition pBetter :: "p ⇒ p ⇒ bool" (infix "≽p" 50) where
  "P ≽p Q  ≡   (promotes P = promotes Q) ∨ (promotes P ≻v promotes Q) " 
(*betterness relation between projects: also reflexive, because two projects can be ranked the same. 
This gives S4 frame*)

(*Tests*)
lemma   " ∀ P Q. (promotes P ≻v promotes Q )  ⟶ (P ≽p Q)" 
  by (simp add: pBetter_def) (*trivial: tested connection b. values ranking and projects betterness*)
lemma pTrans:  "P ≽p Q ⟹ Q ≽p R ⟹ P ≽p R" 
  unfolding pBetter_def vGreater_def  by fastforce

(*Tests with concrete values:*)
lemma "∀ P Q. (( A1 = promotes P) ∧ (B3 = promotes Q)) ⟶ (P ≽p Q)" 
  unfolding pBetter_def vGreater_def vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by simp
lemma "∀ P Q. (( B2 = promotes P) ∧ (C1 = promotes Q)) ⟶ (P ≽p Q)" 
 unfolding pBetter_def vGreater_def vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def  by auto
lemma "∀ P Q. (( B2 = promotes P) ∧ (C1 = promotes Q)) ⟶ (Q ≽p P)"
  nitpick (*ctm as expected*) oops
lemma "∀ P Q. (( A1 = promotes P) ∧ (A1 = promotes Q)) ⟶ (P ≽p Q)"
 unfolding pBetter_def vGreater_def vGreater_def cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def   by simp

(*We define a second betterness relation for projects promoting clusters; this is based on ranking of clusters:*)
(*(* Each Smart City project  has an incidence relation I indicating which values it promotes. *)
consts I :: "  p ⇒ Value ⇒ bool"   (* I p v means that project p  promotes value v *)
abbreviation Iset :: "  p ⇒ Value set" where
  "Iset p ≡ {v. v = promotes p }"   (* The set of values promoted in project p *)*)

abbreviation Iset :: "p ⇒ cluster" where
  "Iset p ≡ cluster_of (promotes p)"
definition clGreater :: "Value set ⇒ Value set ⇒ bool"  (infix "≻cl" 50) where 
  "v ≻cl w  ≡  (cluster_rank v > cluster_rank w)"
definition pBetter2 :: "p ⇒ p ⇒ bool" (infix "≽p2" 50) where 
  "P ≽p2 Q  ≡   (Iset P = Iset Q) ∨ (Iset P ≻cl Iset Q) " 

(*Tests:*)
lemma "∀ P Q. (( B = Iset P) ∧ (C = Iset Q)) ⟶ (P ≽p2 Q)" 
  unfolding pBetter_def vGreater_def  cluster_rank_def cluster_of_def
            cluster_A_def cluster_B_def cluster_C_def clGreater_def pBetter2_def   by auto
lemma "∀ P Q. (( C = Iset P) ∧ (A = Iset Q)) ⟶ (P ≽p2 Q)" 
  nitpick (*ctm as expected*) oops
lemma exists_best_cluster_project:
  assumes "∃P. ∀Q. Iset P ≻cl Iset Q"
  shows   "∃P. ∀Q. P ≽p2 Q"   using assms clGreater_def by auto

text ‹A project can promote multiple values: in this case, it is enough to know the top value for each project 
in order to know which is the best project in a comparison: in this case, the other values are considered equivalent. 
This is a Ceteris paribus situation interpreted as epistemic negative (e.g. "I am not concerned by what I do not know"). 
First, we need to introduce third version of the betterness relation between projects, because we need
to establish that, in case a project promotes a set of values, the betterness is defined on the 
highest ranked value in the set of values that the project promotes.›

definition best_val :: "p ⇒ Value" where
  "best_val P ≡ (SOME v. v ∈ promotes_set P ∧ (∀ w ∈ promotes_set P. intra_rank v ≤ intra_rank w))"

(*lemma best_val_in_set: "best_val P ∈ promotes_set P"
  unfolding best_val_def using set_nonempty sledgehammer

lemma best_val_min: "w ∈ promotes_set P ⟹ intra_rank (best_val P) ≤ intra_rank w"
  unfolding best_val_def using set_nonempty
  by (rule someI2_ex)  (auto intro: Min_le)*)

definition pBetter3  :: "p ⇒ p ⇒ bool" (infix "≽p3" 50) where
  "P ≽p3 Q  ≡  intra_rank (best_val P) ≤ intra_rank (best_val Q)"

definition Iset2 :: "p ⇒ Value set" where "Iset2 P ≡ { v. v ∈ promotes_set P }"

(*Here below the ceteris paribus is introduced, from Benzm\"uller and Fuenmayor: 
for every variable in Γ, P and Q give the same truth value. 
In our semantics this corresponds to say that whatever value is in Γ, either both projects promote it
 or neither does.*)
definition cp_projects ("_❙≡⇩__") where "P ❙≡⇩Γ Q ≡ ∀v. v ∈ Γ ⟶ (v ∈ Iset2 P ⟷ v ∈ Iset2 Q)"
definition cp_projects_better ("_❙⊵⇩__") where "P ❙⊵⇩Γ Q ≡ ( P ≽p3 Q) ∧ (P ❙≡⇩Γ Q)"
lemma "P = Q ⟶ P ❙⊵⇩Γ Q " (*confirmed reflexive*) 
  by (simp add: cp_projects_better_def cp_projects_def pBetter3_def)

lemma
  assumes "A1 ∈ Iset2 P"    and "A1 ∉ Γ"
  and "∀ Q. ¬ A1 ∈ Iset2 Q" and "B1 ∉ Γ"
      and "P ❙≡⇩Γ Q"
(*      and "∀v. v ∈ Iset2 Q ∧ v ∉ Γ ⟶ A1 ≻v v"*) (*no need to assume that A1 outreaches all other values.*)
and NonEmpty:  "∃v. v ∈ Iset2 Q ∧ v ∉ Γ"
and ΓNonEmpty : "∃ w. w ∈  Γ"
  shows   "P ❙⊵⇩Γ Q" 
  using assms(1) assms(3) by auto
 
(*definition projset_preferred :: "Value set ⇒ Value set ⇒ bool" where
  "projset_preferred S T ≡ (∃ v ∈ S. ∀ u ∈ T. rank v > rank u)"
definition project_preferred :: " p ⇒  p ⇒ bool" where
  "project_preferred w1 w2 ≡ projset_preferred (Iset w1) (Iset w2)"

(* In this ontology, one project is preferred over another if the highest-ranked value it promotes 
   is ranked higher than the highest value promoted by the other. *)
lemma pref_higher_value:
  assumes "∃ v ∈ Iset w1. ∀ u ∈ Iset w2. rank v > rank u"
  shows "project_preferred w1 w2"
  using assms project_preferred_def projset_preferred_def by auto*)

end

(********************************************************************************************************************)

text  ‹In Ontology_Flex things are different: The preference between projects varies because 
it is parametrized by conditions e.g. needed values  (a smart city wants to promote specific values and 
select the projects accordingly). This requires the introduction of a possible worlds semantics, 
where, in the context of our application, the possible worlds are interpreted as possible smart cities.›

locale Ontology_Flex =
  fixes  raw_SCV :: "w ⇒ Value set" (* Raw value set parametric on worlds *) and
         raw_NV  :: "Value set"  (*Raw set of needed values, according to specific policies/requirements/guidelines. 
                                  Not parametric on worlds because it is assumed to hold everywhere*) and
         Smart_City_Values :: "w ⇒ Value set" and
         NeededVals :: "Value set" (*These last two constants are used for the following theory-specific definitions:*)
        defines SCV_def:   "Smart_City_Values w ≡ raw_SCV w ∩ (A ∪ B ∪ C)" (*Specification of the value set for this theory*)
         and NV_def:   "NeededVals ≡ raw_NV ∩ (A ∪ B ∪ C)" (*Specification of the needed values for this theory*)
begin

(*Alt:

abbreviation Smart_City_Values :: "w ⇒ Value set" where "Smart_City_Values w ≡ raw_SCV w ∩ (A ∪ B ∪ C)"
abbreviation NeededVals :: "Value set" where  "NeededVals ≡ raw_NV ∩ (A ∪ B ∪ C)" *)

(*Test (trivial): both are subset of the union of clusters*)
lemma  "Smart_City_Values w ⊆ (A ∪ B ∪ C)" 
  unfolding SCV_def by auto
lemma   "NeededVals ⊆ (A ∪ B ∪ C)"
  unfolding NV_def by auto

(*We define the "smart values" in a world as the intersection of the values in this world with the needed values:*)
definition smart_values :: "w ⇒ Value set" where (* values in a possible world (AKA possible Smart City) that meet the needed values*)
  "smart_values w = Smart_City_Values w ∩ NeededVals"

(*Based on this, we define the weak betterness relation between worlds AKA possible Smart Cities: 
a smart city X is better than smart city Y if Y's values that meet the needed values are a subset of X's values 
that meet the needed values:*)
definition better_world :: "w ⇒ w ⇒ bool"  (infix "≽⇧w" 50) where 
  "w ≽⇧w v ≡ smart_values v ⊆ smart_values w" 

(*Tests (trivial): we have S4*)
lemma refl: "w ≽⇧w w"  by (simp add: better_world_def)
lemma trans: "w ≽⇧w v ⟹ v ≽⇧w u ⟹ w ≽⇧w u"  unfolding better_world_def by (meson order.trans)
lemma  "(w ≽⇧w v) ∧ (v ≽⇧w w)" nitpick oops (*ctm expected*)
lemma "w ≽⇧w v ⟹ v ≽⇧w w ⟹ smart_values w = smart_values v" 
  using better_world_def by auto (*antisymmetric up to extensional equality of the value sets*)

(*We also define the strong variant - irreflexive:*)
definition better_strict_world :: "w ⇒ w ⇒ bool"  (infix "≻⇧w" 60) where 
  "w ≻⇧w v ≡ w ≽⇧w v ∧ ¬ v ≽⇧w w"   

end

(*Now we run some tests, in a sublocale:*)

locale Two_Worlds_Test = Ontology_Flex +
  fixes W V :: w (*fixing two worlds*)
  assumes NV_specif: "NeededVals = {A1, A3, B2, B3, C1, C3}"
      and SCV_W:  "Smart_City_Values W = {A1, A3, B1, B3}"
      and SCV_V:  "Smart_City_Values V = {A1, A2, B1, C2}"
begin

lemma smart_W: "smart_values W = {A1, A3, B3}"
using NV_specif SCV_W
  unfolding smart_values_def SCV_def NV_def
            cluster_A_def cluster_B_def cluster_C_def   by auto

lemma smart_V: "smart_values V = {A1}"
using NV_specif SCV_V
  unfolding  smart_values_def  SCV_def  NV_def 
  cluster_A_def cluster_B_def cluster_C_def   by simp

lemma W_better_V:  " W ≽⇧w V"
  using smart_W smart_V
  unfolding smart_values_def SCV_def NV_def better_world_def       by simp

end


locale Ontology_Card = Ontology_Flex + Two_Worlds_Test
begin

text ‹In Ontology_Card I introduce a variant of the betterness relation between worlds that is based on cardinality.
 Now a world X is better than Y iff the cardinality of the intersection between X's values and the needed values 
is greater than the cardinality of the values of Y  with the needed values:›

definition better_card :: "w ⇒ w ⇒ bool"  (infix "≽⇧c" 50) where 
  "w ≽⇧c v ≡ (card (smart_values w)) ≥ (card (smart_values v))"

definition better_card_strong :: "w ⇒ w ⇒ bool"  (infix "≻⇧c" 60) where
  "w ≻⇧c v ≡ card (smart_values w) > card (smart_values v)"

(*Basic algebric tests: weak is a pre-order, strong is  irreflexive & transitive:*)
lemma card_refl: "w ≽⇧c w" 
  by (simp add: better_card_def)
lemma card_trans:  "w ≽⇧c v ⟹ v ≽⇧c u ⟹ w ≽⇧c u"
  by (meson better_card_def le_trans)
lemma strict_imp_weak:  "w ≻⇧c v ⟹ w ≽⇧c v" 
  by (simp add: better_card_def better_card_strong_def)
lemma strong_card_irrefl: "¬ w ≻⇧c w"
  by (simp add: better_card_strong_def)
lemma strict_trans:   "w ≻⇧c v ⟹ v ≻⇧c u ⟹ w ≻⇧c u" 
  using better_card_strong_def order.strict_trans by blast

(*We evoke the previous concrete cases, W and V:*)

lemma smart_W_card: "card (smart_values W) = 3"
  using  smart_W by simp

lemma smart_V_card: "card (smart_values V) = 1"
  using smart_V by simp

lemma W_strictly_better_V_q: "W ≻⇧c V"
  unfolding better_card_strong_def smart_W_card smart_V_card   by simp

end
                                     
locale Preference_Projects = Ontology_Flex + Two_Worlds_Test + Ontology_Card

begin

text ‹The previous locales Ontology_Flex and Ontology_Card were needed to reason about projects. 
Indeed, the fact that a specific world (or set of worlds) has some values means that there is a project in that world 
(AKA Smart City) that promotes these values. Hence, we need now to establish a preference relation for the projects.
This time, the preference between projects is based not on a value  ranking (like in Ontology_Fix), 
but on the order between worlds: the project preference is the order lifted to possible worlds. 
In other words  the order is applied to world-lifted propositions: the project preference is hence encoded as 
λ-expressions (higher-order functions) parametized on worlds (elements of type w). Informally, this means that
  a project is preferred to another one iff the Smart Cities that implement this projects  are better than
 the Smart Cities that implement the other project.
I introduce two preference relations, one based on the subset version,
 and another one based on the cardinality version:*) ›

(*preference between projects, based on the subset version, with all quantifier permutations:*)
abbreviation preferenceEA :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧E⇧A" 45)
 where "φ ≽⇧E⇧A ψ ≡  λ w. ∃ u. φ u ∧ (∀ v. ψ v ⟶ u ≽⇧w v)"
abbreviation preferenceEE :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧E⇧E" 45)
 where "φ ≽⇧E⇧E ψ ≡  λ w. ∃ u. φ u ∧ (∃ v. ψ v ∧ u ≽⇧w v)"
abbreviation preferenceAE :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧A⇧E" 45)
 where "φ ≽⇧A⇧E ψ ≡  λ w. ∀ u. φ u ⟶ (∃ v. ψ v ∧ u ≽⇧w v)"
abbreviation preferenceAA :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧A⇧A" 45)
 where "φ ≽⇧A⇧A ψ ≡  λ w. ∀ u. φ u ⟶ (∀ v. ψ v ⟶ u ≽⇧w v)"

(*We make the tests with concrete projects:*)

lemma P_pref_Q :
  fixes  P Q :: "w ⇒ bool"
  assumes NV:   "NeededVals = {A1, A3, C3}"
      and svP:  "∀w. P w ⟶ Smart_City_Values w = {A1, A3, B3, C3}" (*Alt: ⋀w. P w ⟹ Smart_City_Values w …*)
      and svQ:  "∀w. Q w ⟶ Smart_City_Values w = {A3, C3, B2}"     
      and P_ex: "∃w. P w"
      and Q_ex: "∃w. Q w"
  shows  "∀w. (P ≽⇧E⇧A Q) w"
proof    
  fix w
  obtain u where Pu: "P u" using P_ex by blast
  have sm_u: "smart_values u = {A1, A3, C3}"  using Pu svP NV
    unfolding smart_values_def SCV_def NV_def by auto
  have sm_v: "∀v. Q v ⟶ smart_values v = {A3, C3}"  using svQ NV
    unfolding smart_values_def SCV_def NV_def by auto
 have dom: "∀v. Q v ⟶ u ≽⇧w v" unfolding better_world_def
  using sm_u sm_v by auto
   have "∃u. P u ∧ (∀v. Q v ⟶ u ≽⇧w v)"   using Pu dom by blast
   thus "(P ≽⇧E⇧A Q) w"   by simp
qed

(*Now the alternative with cardinality, with all quantifier permutations:*)
abbreviation preferenceEA_card :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧E⇧A⇩C" 45)
 where "φ ≽⇧E⇧A⇩C ψ ≡  λ w. ∃ u. φ u ∧ (∀ v. ψ v ⟶ u ≽⇧c v)"
abbreviation preferenceEE_card :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧E⇧E⇩C" 45)
 where "φ ≽⇧E⇧E⇩C ψ ≡  λ w. ∃ u. φ u ∧ (∃ v. ψ v ∧ u ≽⇧c v)"
abbreviation preferenceAE_card :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧A⇧E⇩C" 45)
 where "φ ≽⇧A⇧E⇩C ψ ≡  λ w. ∀ u. φ u ⟶ (∃ v. ψ v ∧ u ≽⇧c v)"
abbreviation preferenceAA_card :: "(w ⇒ bool) ⇒ (w ⇒ bool) ⇒ (w ⇒ bool)"  (infix "≽⇧A⇧A⇩C" 45)
 where "φ ≽⇧A⇧A⇩C ψ ≡  λ w. ∀ u. φ u ⟶ (∀ v. ψ v ⟶ u ≽⇧c v)"

(*Test:*)

lemma P_pref_Q_card:
  fixes  P Q :: "w ⇒ bool"
  assumes NV:   "NeededVals = {A1, A3, C3}"
      and svP:  "∀w. P w ⟶ Smart_City_Values w = {A1, A3, B3, C3}" (*Alt: ⋀w. P w ⟹ Smart_City_Values w...*)
      and svQ:  "∀w. Q w ⟶ Smart_City_Values w = {A3, C3, B2}"
      and P_ex: "∃w. P w"
      and Q_ex: "∃w. Q w"
  shows  "∀w. (P ≽⇧E⇧A⇩C Q) w"
proof         
  obtain u where Pu: "P u" using P_ex by blast
  have card_u: "card (smart_values u) = 3"   using Pu svP NV
    unfolding smart_values_def SCV_def NV_def   by simp
  have card_v: "∀v. Q v ⟶ card (smart_values v) = 2"
    using svQ NV unfolding smart_values_def SCV_def NV_def by simp
have dom: "∀v. Q v ⟶ u ≽⇧c v"
  unfolding better_card_def using card_u card_v   by simp
  have "∃u. P u ∧ (∀v. Q v ⟶ u ≽⇧c v)" using Pu dom by blast
  thus "(P ≽⇧E⇧A⇩C Q) w" by simp
qed

end

end