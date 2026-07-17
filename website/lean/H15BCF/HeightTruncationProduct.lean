/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.GenusOneProduct

/-!
# Height truncations of the genus-one xi product

The infinite product in `GenusOneProduct` is indexed by the subtype of all
nontrivial zeros, while the BCF finite products are indexed by height-truncated
`Finset`s of complex numbers.  This file proves that the latter finite sets are
cofinal among finite zero subsets.  Consequently, any pointwise multipliable
genus-one product converges along the actual BCF height truncations.

This is a finite-set/filter argument only.  It does not prove summability,
local uniformity, or logarithmic-derivative convergence; those remain the
analytic inputs isolated elsewhere.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The embedding from a fixed height truncation into the subtype of all
nontrivial zeta zeros. -/
def bcfZeroHeightSubtypeEmbedding (T : ℝ) :
    (↥(bcfZerosUpToHeight T) ↪ bcfNontrivialZetaZeros) where
  toFun rho := ⟨rho, by
    have hrho : (rho : ℂ) ∈ bcfZerosUpToHeight T := rho.property
    rw [mem_bcfZerosUpToHeight] at hrho
    rw [mem_bcfNontrivialZetaZeros]
    exact ⟨hrho.1, hrho.2.1, hrho.2.2.1⟩⟩
  inj' x y h := by
    apply Subtype.ext
    exact congrArg (fun z : bcfNontrivialZetaZeros ↦ (z : ℂ)) h

/-- The height-truncated nontrivial zeros, now as a `Finset` in the common
subtype used by the infinite product. -/
def bcfZerosUpToHeightSubtype (T : ℝ) : Finset bcfNontrivialZetaZeros :=
  (bcfZerosUpToHeight T).attach.map (bcfZeroHeightSubtypeEmbedding T)

/-- The height-truncated subtype `Finset`s are cofinal in the directed set of
all finite subsets of nontrivial zeros. -/
theorem tendsto_bcfZerosUpToHeightSubtype_atTop :
    Tendsto bcfZerosUpToHeightSubtype atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro S
  let M : ℝ := ∑ rho ∈ S, |(rho : ℂ).im|
  filter_upwards [eventually_ge_atTop M] with T hT
  intro rho hrho
  unfold bcfZerosUpToHeightSubtype
  rw [Finset.mem_map]
  have hbound : |(rho : ℂ).im| ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (s := S) (f := fun eta : bcfNontrivialZetaZeros ↦ |(eta : ℂ).im|)
      (fun _ _ ↦ abs_nonneg _) hrho
  have hraw : (rho : ℂ) ∈ bcfZerosUpToHeight T := by
    rw [mem_bcfZerosUpToHeight]
    have hnontrivial := mem_bcfNontrivialZetaZeros.mp rho.property
    exact ⟨hnontrivial.1, hnontrivial.2.1, hnontrivial.2.2, hbound.trans hT⟩
  refine ⟨⟨(rho : ℂ), hraw⟩, Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  rfl

/-- Reindexing the BCF finite product through the subtype embedding leaves it
unchanged. -/
theorem bcfXiFiniteGenusOneProduct_eq_prod_heightSubtype (T : ℝ) (s : ℂ) :
    bcfXiFiniteGenusOneProduct T s =
      ∏ rho ∈ bcfZerosUpToHeightSubtype T,
        bcfXiGenusOneFactor (rho : ℂ) s := by
  unfold bcfXiFiniteGenusOneProduct bcfZerosUpToHeightSubtype
  rw [Finset.prod_map]
  change (∏ rho ∈ bcfZerosUpToHeight T, bcfXiGenusOneFactor rho s) =
    ∏ rho ∈ (bcfZerosUpToHeight T).attach,
      bcfXiGenusOneFactor (rho : ℂ) s
  exact (Finset.prod_attach (bcfZerosUpToHeight T)
    (fun rho : ℂ ↦ bcfXiGenusOneFactor rho s)).symm

/-- Pointwise multipliability of the genus-one factors gives convergence of
the concrete BCF finite products as their height cutoff tends to infinity. -/
theorem tendsto_bcfXiFiniteGenusOneProduct_atTop
    (hprod : BCFGenusOneProductPointwiseMultipliable) (s : ℂ) :
    Tendsto (fun T : ℝ ↦ bcfXiFiniteGenusOneProduct T s) atTop
      (𝓝 (bcfXiInfiniteGenusOneProduct s)) := by
  have hprod' :
      Tendsto
        (fun S : Finset bcfNontrivialZetaZeros ↦
          ∏ rho ∈ S, bcfXiGenusOneFactor (rho : ℂ) s)
        atTop (𝓝 (bcfXiInfiniteGenusOneProduct s)) :=
    hprod s |>.hasProd
  have hheight := hprod'.comp tendsto_bcfZerosUpToHeightSubtype_atTop
  refine hheight.congr' ?_
  filter_upwards with T
  exact (bcfXiFiniteGenusOneProduct_eq_prod_heightSubtype T s).symm

/-- The previously isolated absolute-convergence target therefore already
gives convergence of the concrete BCF height products. -/
theorem tendsto_bcfXiFiniteGenusOneProduct_atTop_of_absoluteConvergence
    (habs : BCFGenusOneProductAbsoluteConvergence) (s : ℂ) :
    Tendsto (fun T : ℝ ↦ bcfXiFiniteGenusOneProduct T s) atTop
      (𝓝 (bcfXiInfiniteGenusOneProduct s)) :=
  tendsto_bcfXiFiniteGenusOneProduct_atTop
    (bcfGenusOneProduct_pointwiseMultipliable_of_absoluteConvergence habs) s

end

end NBMellinTools.H15BCF
