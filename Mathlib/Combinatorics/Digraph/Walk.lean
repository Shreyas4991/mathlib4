/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Batteries
/-!
# Walks and Paths

This module defines walks and paths on directed graphs.
-/

namespace Digraph

universe u

variable {V : Type u}

@[ext]
structure Walk (G : Digraph V) where
  support : List V
  non_empty_support : support ≠ []
  chainAdj : List.IsChain G.Adj support

namespace Walk

def startsAt {G : Digraph V} (W : G.Walk) : V :=
  W.support.head W.non_empty_support

def endsAt {G : Digraph V} (W : G.Walk) : V :=
  W.support.getLast W.non_empty_support

def length {G : Digraph V} (W : G.Walk) :=
  W.support.length - 1

def Single {G : Digraph V} (u : V) : G.Walk where
  support := [u]
  non_empty_support := by simp
  chainAdj := by
    apply List.IsChain.singleton

def head {G : Digraph V} (W : G.Walk) : V :=
  W.support.head W.non_empty_support

def cons {G : Digraph V}
  (u : V) (W : G.Walk)
  (hAdj : G.Adj u W.head)
  : G.Walk where
  support :=
    match W.support with
    | [] => [u]
    | v :: vs => u :: v :: vs
  chainAdj := by
    have hchainW := W.chainAdj
    cases hW : W.support with
    | nil =>
        simp
    | cons head tail =>
        simp only [List.isChain_cons_cons]
        rw [hW] at hchainW
        constructor
        · simp_all only [Walk.head, List.head_cons]
        · assumption
  non_empty_support := by
    cases W.support <;> simp

def tail {G : Digraph V} (W : G.Walk) (hW : W.support.length ≥ 2) : G.Walk where
  support := W.support.tail
  chainAdj := by
    apply List.IsChain.tail
    exact W.chainAdj
  non_empty_support := by
    cases h : W.support with (simp_all only [List.length_nil, ge_iff_le, nonpos_iff_eq_zero,
      OfNat.ofNat_ne_zero])
    | cons head tail =>
        cases htail : tail with (simp_all)

@[simp]
lemma head_single {G : Digraph V} (W : G.Walk) (v : V)
  (hSingle : W = Walk.Single v) : W.head = v := by
  rw [hSingle]
  simp only [head, Single, List.head_cons]

@[simp]
lemma head_cons_eq {G : Digraph V}
  (W : G.Walk) (v : V) (hadj : G.Adj v W.head) :
  (Walk.cons v W hadj).head = v := by
  simp only [head]
  cases h : W.support with (simp only [cons, h, List.head_cons])

@[simp]
lemma Walk_length_two_decompose {G : Digraph V}
  (W : G.Walk) (hW : W.support.length ≥ 2) :
  ∃ v w : V, ∃ rest : List V, W.support = v :: w :: rest := by
  match h : W.support with
  | [] =>
      have : W.support.length = 0 := by
        simp_all
      exfalso
      omega
  | [v] =>
      have : W.support.length = 1 := by
        simp_all
      exfalso
      omega
  | v :: w :: rest =>
      use v, w, rest



@[simp]
lemma cons_support_eq_support_cons {G : Digraph V}
  (W : G.Walk) (v : V) (hadj : G.Adj v W.head) :
  (Walk.cons v W hadj).support = v :: W.support := by
  simp only [cons]
  cases W.support with (simp only)

lemma Walk_Adj_head {G : Digraph V} (W : G.Walk)
  (hW : W.support.length ≥ 2) :
  G.Adj W.support[0] ((W.tail hW).support.head (W.tail hW).non_empty_support) := by
  apply Walk_length_two_decompose at hW
  obtain ⟨v, w, rest, hW⟩ := hW
  simp [tail, hW]
  have chain := W.chainAdj
  rw [hW] at chain
  simp at chain
  tauto


lemma Walk_is_cons_of_head_tail {G : Digraph V}
  (W : G.Walk) (hW : W.support.length ≥ 2) :
  W = Walk.cons W.support[0] (W.tail hW) (by apply Walk_Adj_head)  := by
  apply Walk.Walk_length_two_decompose at hW
  obtain ⟨v, w, rest, hW⟩ := hW
  have adj := W.chainAdj
  simp[hW] at adj
  ext i v
  simp_all only [List.getElem_cons_zero, tail, List.tail_cons, cons_support_eq_support_cons]

def IsCircuit {G : Digraph V} (W : G.Walk) : Prop :=
  W.support.length > 2 ∧ G.Adj W.support.head W.support.getLast

def edgeList {G : Digraph V} (W : G.Walk) : List <| V × V :=
  match hW : W.support with
  | []
  | [_] => []
  | v :: w :: ws =>
      (v,w) :: (edgeList <| W.tail (by simp [hW]))
  termination_by W.support.length
  decreasing_by
    simp [Walk.tail, hW]

lemma isWalkEdge_vert_support_left (G : Digraph V)
  (W : G.Walk) (x y : V) (hxy : (x, y) ∈ W.edgeList)
  : x ∈ W.support := by
  revert hxy
  fun_induction Walk.edgeList
  · simp_all
  · grind
  case case3 W' v w ws W'supp ih1=>
    simp_all only [List.mem_cons, Prod.mk.injEq]
    rintro (⟨x_eq_v, y_eq_w⟩ | hrest)
    · left
      assumption
    · specialize ih1 hrest
      have : (W'.tail (by grind)).support = w :: ws := by
        simp only [Walk.tail, W'supp, List.tail_cons]
      rw [this] at ih1
      right
      exact List.eq_or_mem_of_mem_cons ih1

lemma isWalkEdge_vert_support_right (G : Digraph V)
  (W : G.Walk) (x y : V) (hxy : (x, y) ∈ W.edgeList)
  : y ∈ W.support := by
  revert hxy
  fun_induction Digraph.Walk.edgeList
  · expose_names
    simp_all
  · expose_names
    grind
  · expose_names
    simp_all only [List.mem_cons, Prod.mk.injEq]
    rintro (⟨x_eq_v, y_eq_w⟩ | hrest)
    · right; left
      assumption
    · expose_names
      specialize ih1 hrest
      right
      have : (x_1.tail (by grind)).support = w :: ws := by
        simp only [Walk.tail, hW, List.tail_cons]
      rw [this] at ih1
      exact List.eq_or_mem_of_mem_cons ih1

abbrev isWalkEdge {G : Digraph V}
  (W : G.Walk) (x y : V) :=
    (x,y) ∈ W.edgeList

@[simp]
def appendByEdge {G : Digraph V} (W W' : G.Walk)
  (hjoin : G.Adj W.endsAt W'.startsAt) : G.Walk where
  support := W.support ++ W'.support
  non_empty_support := by
    exact List.append_ne_nil_of_left_ne_nil W.non_empty_support W'.support
  chainAdj := by
    have W_adj := W.chainAdj
    have W'_adj := W'.chainAdj
    cases h : W'.support with
    | nil =>
        simp_all
    | cons head tail =>
        refine List.isChain_append.mpr ?_
        simp_all only [Option.mem_def, List.head?_cons, Option.some.injEq, forall_eq', true_and]
        intro x hx
        have s₁ : head = W'.startsAt := by
          simp [startsAt, h]
        have s₂ : x = W.endsAt := by
          simp only [endsAt]
          exact Eq.symm (List.getLast_of_mem_getLast? hx)
        rw [s₁, s₂]
        exact hjoin

@[simp]
lemma append₁_startsAt {G : Digraph V}
  (W₁ W₂ : G.Walk) (h12 : G.Adj W₁.endsAt W₂.startsAt)
  : (W₁.appendByEdge W₂ h12).startsAt = W₁.startsAt := by
  simp only [startsAt, appendByEdge]
  exact List.head_append_left W₁.non_empty_support

@[simp]
lemma append₁_endsAt {G : Digraph V}
  (W₁ W₂ : G.Walk) (h12 : G.Adj W₁.endsAt W₂.startsAt)
  : (W₁.appendByEdge W₂ h12).endsAt = W₂.endsAt := by
  simp only [appendByEdge, endsAt]
  exact
    List.getLast_append_of_ne_nil
      (id (Eq.refl (W₁.support ++ W₂.support)) ▸ (W₁.appendByEdge W₂ h12).non_empty_support)
      W₂.non_empty_support

@[simp]
def appendByVertex {G : Digraph V} (W W' : G.Walk)
  (heq : W.endsAt = W'.startsAt) : G.Walk where
  support := W.support ++ W'.support.tail
  non_empty_support := by
    apply List.append_ne_nil_of_left_ne_nil W.non_empty_support
  chainAdj := by
    have W_adj := W.chainAdj
    have W'_adj := W'.chainAdj
    cases hW'support : W'.support with
    | nil =>
        simp_all
    | cons W'head W'tail =>
        refine List.isChain_append.mpr ?_
        simp_all only [List.tail_cons, Option.mem_def, true_and]
        constructor
        · exact List.isChain_of_isChain_cons W'_adj
        · have s₁ : W'.startsAt = W'head := by
            simp_all [startsAt]
          rw [←s₁] at hW'support
          intro x x_is_Wlast
          -- Prove that x is actually W'head
          have s₂ : W.support.getLast W.non_empty_support = x := by
            exact List.getLast_of_mem_getLast? x_is_Wlast
          have s₃ : W.endsAt = x := by
            exact s₂
          simp_all only
          -- now deal with W'tail and y
          intro y hW'tail
          cases hW'tail' : W'tail with
          | nil =>
              simp_all
          | cons W'tail'head W'tail'tail =>
              rw [hW'tail'] at W'_adj
              simp at W'_adj
              simp only [hW'tail', List.head?_cons, Option.some.injEq] at hW'tail
              rw [←hW'tail]
              exact W'_adj.left

@[simp]
lemma appendByVertex_startsAt {G : Digraph V}
  (W₁ W₂ : G.Walk) (h12 : W₁.endsAt = W₂.startsAt)
  : (W₁.appendByVertex W₂ h12).startsAt = W₁.startsAt := by
  simp only [startsAt, appendByVertex]
  exact List.head_append_left W₁.non_empty_support

@[simp]
lemma appendByVertex_endsAt {G : Digraph V}
  (W₁ W₂ : G.Walk) (h12 : W₁.endsAt = W₂.startsAt)
  : (W₁.appendByVertex W₂ h12).endsAt = W₂.endsAt := by
  cases h₂ : W₂.support with
  | nil =>
      exfalso
      exact W₂.non_empty_support h₂
  | cons head tail =>
      cases htail : tail with
      | nil =>
          simp_all
          simp [startsAt, endsAt, h₂]
      | cons thead ttail =>
          have : tail ≠ [] := by
            simp only [htail, ne_eq, reduceCtorEq, not_false_eq_true]
          simp only [endsAt, appendByVertex]
          simp_rw [h₂, htail]
          simp

lemma cons_induction {G : Digraph V}
  (motive : G.Walk → Prop)
  (base : (v : V) → motive ⟨[v], by simp, List.IsChain.singleton v⟩)
  (ind : (v : V) → (W : G.Walk)
      → motive W → (hadj : G.Adj v (W.support.head W.non_empty_support))
      → motive (Walk.cons v W hadj)) : (W : G.Walk) → motive W := by
    intro W
    induction h : W.support generalizing W with
    | nil =>
        exfalso
        exact W.non_empty_support h
    | cons head tail ih =>
        cases htail : tail with
        | nil =>
            rw [htail] at h
            have s₁ : W = ⟨[head], by simp, List.IsChain.singleton head⟩ := by
              simp_all only
              ext i v
              simp [h]
            rw [s₁]
            exact (base head)
        | cons thead ttail =>
            have s₁ : W.support.length ≥ 2 := by
              simp_all only [List.length_cons, ge_iff_le,
                le_add_iff_nonneg_left, zero_le]
            have s₂ : (W.tail s₁).support = tail := by
              simp_all [Walk.tail]
            let Wtail : G.Walk := W.tail s₁
            have s₄ : motive Wtail := by
              specialize ih Wtail (by simp [Wtail, s₂])
              exact ih
            have s₅ : G.Adj head (Wtail.support.head Wtail.non_empty_support) := by
              simp_all only [Walk.tail, List.tail_cons,
                List.head_cons, Wtail]
              have h₁ := W.chainAdj
              rw [h] at h₁
              simp at h₁
              exact h₁.left
            specialize ind head Wtail s₄ s₅
            have s₆ : W = Walk.cons head Wtail s₅ := by
              have h₁ : head = W.support[0] := by
                simp_all only [List.getElem_cons_zero]
              simp_rw [h₁]
              apply Walk.Walk_is_cons_of_head_tail
            rw [s₆]
            exact ind

lemma append_induction {G : Digraph V}
  (motive : G.Walk → Prop)
  (base : (v : V) → motive ⟨[v], by simp, List.IsChain.singleton v⟩)
  (ind : (W : G.Walk) → (v : V)
      → motive W → (hadj : G.Adj W.endsAt v)
      → motive (Walk.appendByEdge W (Walk.Single v) hadj)) (W : G.Walk) : motive W := by
  induction hW : W.support generalizing W with
  | nil =>
      exfalso
      exact W.non_empty_support hW
  | cons head tail ih =>
    cases tail with
    | nil =>
        specialize base head
        have s₁ : W = {
            support := [head],
            non_empty_support := by simp
            chainAdj := by simp } := by
          ext
          simp_all
        rw [s₁]
        exact base
    | cons thead ttail =>
        let Wtail := W.tail (by simp[hW])
        specialize ih Wtail (by simp [Wtail, tail, hW])

        sorry


end Walk

structure Path (G : Digraph V) extends Walk G where
  nodup : List.Nodup support

namespace Path

def Single {G : Digraph V} (u : V) : G.Path where
  support := [u]
  non_empty_support := by simp
  chainAdj := by
    apply List.IsChain.singleton
  nodup := by
    simp_all

def IsCycle (G : Digraph V) (P : G.Path) : Prop :=
  P.toWalk.IsCircuit

def cons {G : Digraph V}
  (u : V) (W : G.Path)
  (hnewvertex : List.Nodup (u :: W.support))
  (hAdj : (hnempty : W.support ≠ [])
    → G.Adj u (W.support.head hnempty))
  : G.Path where
  support :=
    match W.support with
    | [] => [u]
    | v :: vs => u :: v :: vs
  non_empty_support := by cases W.support <;> simp
  chainAdj := by
    have hchainW := W.chainAdj
    cases hW : W.support with
    | nil =>
        simp
    | cons head tail =>
        simp only [List.isChain_cons_cons]
        rw [hW] at hchainW hAdj
        constructor
        · simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head_cons, forall_const]
        · assumption
  nodup := by
    induction hW : W.support with
    | nil =>
        simp
    | cons head tail ih =>
        simp_all



abbrev isPathEdge {G : Digraph V}
  (P : G.Path) (x y : V) :=
    (x,y) ∈ P.edgeList

abbrev PathFromTo {G : Digraph V} (P : G.Path) (s t : V) :=
  P.startsAt = s  ∧ P.endsAt = t



def length {G : Digraph V} (P : G.Path) := P.support.length - 1

end Path

end Digraph
