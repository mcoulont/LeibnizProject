
import Articles.ethics_in_society
import Articles.definition_capitalism_communism

namespace only_capitalism_makes_independent

variable {Individual : Type}
variable {eqInd : DecidableEq Individual}
variable {Individuals : Fintype Individual}

open Fintype
open definition_capitalism_communism ethics_in_society

def retribution_depends_only_on_own_contribution
(redi : @Redistribution Individual Individuals) :
Prop :=
  ∃ (f : MonetaryValue -> MonetaryValue),
  ∀ (cont : @Profile Individual MonetaryValue) (i : Individual),
    redi.val cont i = f (cont i)

lemma retribution_depends_only_on_own_contribution_capitalism :
retribution_depends_only_on_own_contribution (
  @pure_capitalism_Redistribution Individual Individuals
) := by
  exists id
  intro cont i
  tauto

theorem only_pure_capitalism_makes_independent
(redi : @Redistribution Individual Individuals) (i0 : Individual) :
retribution_depends_only_on_own_contribution redi <->
redi = @pure_capitalism_Redistribution Individual Individuals := by
  apply Iff.intro
  rotate_left
  · intro pc
    rewrite [pc]
    apply retribution_depends_only_on_own_contribution_capitalism
  · intro rdoc
    have sumc := redi.property
    --simp at sumc
    ext cont
    unfold retribution_depends_only_on_own_contribution at rdoc
    obtain ⟨retr, rdo⟩ := rdoc
    unfold pure_capitalism_Redistribution
    simp
    unfold pure_capitalism
    have defretr : retr = id := by
      apply funext
      intro mv
      specialize (rdo (fun _ => mv))
      unfold preserves_total at sumc
      specialize (sumc (fun _ => mv))
      unfold total_value at sumc
      --simp at rdo
      apply sum_congr at rdo
      rewrite [rdo] at sumc
      simp at sumc
      rcases sumc with eqrmv|emp
      rotate_left
      · have inh : Fintype.card Individual ≠ 0 := inhabited_implies_nonnull_card i0
        tauto
      · tauto
    specialize (rdo cont)
    apply funext
    intro i
    specialize (rdo i)
    rewrite [defretr] at rdo
    tauto

end only_capitalism_makes_independent
