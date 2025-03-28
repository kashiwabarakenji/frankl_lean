# A Lean 4 Approach to Frankl's Conjecture: The Case of Ideal Families

## Abstract

Frankl's conjecture (also known as the union-closed set conjecture) is a long-standing unsolved problem in combinatorics. Here, we focus on a special type of set families defined over a finite ground set, which are closed under intersections and include both the ground set and the empty set as elements. Frankl's conjecture states that such a set family must contain a rare vertex. A vertex is considered rare if the number of hyperedges (elements of the set family) containing the vertex is at most half the total number of hyperedges.

Although this conjecture remains unresolved in general, it has been proven for certain specific classes of set families. One such class is the **ideal families**, which are defined as set families containing both the empty set and the ground set, and for which all hyperedges other than the ground set are closed under subsets. It is straightforward to verify that ideal families are also closed under intersections. This work focuses on the ideal families.

A set family is considered **rare on average** if the total size of all hyperedges is at most half the product of the number of vertices (i.e., the size of the ground set) and the total number of hyperedges. If a set family is rare on average, it is easy to show that it contains at least one rare vertex. This is because the total size of all hyperedges equals the sum of the degrees of all vertices, a result derived from the double counting principle.

Demonstrating that ideal families are rare on average (i.e., the quantity `2 * (sum of hyperedge sizes) - (size of the ground set) * (number of hyperedges)` is negative) may appear straightforward at first glance, but proving it rigorously is more challenging than it seems. In this study, we first construct a proof of this claim manually and then formalize it using Lean 4 to verify its correctness. This GitHub repository contains the Lean 4 formalization of the proof.

Lean 4 is a system that allows formal descriptions of mathematical statements and proofs, providing rigorous correctness guarantees.

---

## On Proof Construction

Although the proof of the theorem may appear intricate, explaining it to another person in natural language might take only about ten minutes. However, formalizing the proof in Lean 4 required approximately 5000 lines of code. As a beginner in Lean 4, it took me around three months to complete the proof.

During the proof construction process in Lean 4, I used various support tools, including ChatGPT Plus, Lean Copilot, and GitHub Copilot. These tools assist in generating proof code and performing simple automated proofs. For instance, ChatGPT can suggest translations of human-written proofs in natural language into Lean 4 syntax. However, the code generated by ChatGPT and GitHub Copilot often contained syntax from older versions like Lean 3 or used theorems from Mathlib 3, requiring substantial manual corrections. In contrast, Lean Copilot provided accurate code for the current version of Lean but could not handle complex proofs. Lean Copilot is particularly useful in near-complete proof states, where only minor steps remain to be formalized.

It is worth noting that proofs generated by Lean Copilot tend to include unnecessary elements, making them less readable than human-written proofs. While my primary goal was to ensure that the proofs passed verification, this resulted in some parts of the proof being less accessible to human readers.

After completing the initial proof, I wrote a corresponding paper and refactored the code to align the formalization with the descriptions in the paper. This process reduced the codebase to approximately 3000 lines, making it more concise and structured.

## Main Theorem and Definitions

The proof of the current theorem in Lean is stored in the `Frankl` folder of this repository. The main result is stated at the end of `FranklMain.lean`:

```lean
theorem ideal_average_rarity (F : IdealFamily α)[DecidablePred F.sets]  :
  F.normalized_degree_sum ≤ 0
```

This theorem demonstrates that the `normalized_degree_sum` of any ideal family with a ground set of size `n` is at most zero, showing that it is rare on average.

Below are the primary definitions used in the proof:

```lean
-- Set families
structure SetFamily (α : Type):=
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)

-- Definition of intersection-closed families
def isIntersectionClosedFamily  (F : SetFamily α) : Prop :=
  ∀ {s t : Finset α}, F.sets s → F.sets t → F.sets (s ∩ t)

-- Definition of rare vertices
def is_rare (F : SetFamily α) (v : α)  [DecidablePred F.sets]  : Prop :=
  2 * F.degree v - F.number_of_hyperedges <= 0

-- Ideal families
structure IdealFamily  (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
  (has_empty : sets ∅)
  (has_ground : sets ground)
  (down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

-- Total size of hyperedges
noncomputable def SetFamily.total_size_of_hyperedges (F : SetFamily α)  [DecidablePred F.sets] : Int :=
   Int.ofNat (((Finset.powerset F.ground).filter F.sets).sum Finset.card)

-- Number of hyperedges
noncomputable def SetFamily.number_of_hyperedges  (F : SetFamily α) [DecidablePred F.sets]: Int :=
  Int.ofNat (Finset.card (Finset.filter (λ s => F.sets s ) (F.ground.powerset)))

-- Normalized degree sum
noncomputable def SetFamily.normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) [DecidablePred F.sets]: ℤ :=
  2 * (F.total_size_of_hyperedges:Int) - (F.number_of_hyperedges:Int)*(F.ground.card:Int)
```

## Minor Operations on Ideal Families

There are three types of operations that create a new ideal family with a smaller ground set from a given Ideal Family: **deletion**, **contraction**, and **trace**.

### **Contraction**
For a set family, the contraction with respect to a vertex \( v \) is defined as the set family obtained by taking all hyperedges \( H \) containing \( v \) and replacing them with \( H \setminus \{v\} \). The contraction operation preserves the downward-closed property of the set family.  
When \(\{v\}\) itself is a hyperedge, the contraction includes the empty set, ensuring that the contraction of an ideal family remains an ideal family.

### **Deletion**
For a set family, the deletion with respect to a vertex \( v \) is defined as the set family obtained by collecting all hyperedges that do not contain \( v \). However, after deletion, the resulting set family may no longer include the ground set, as \( \text{ground} \setminus \{v\} \) might not be a hyperedge. To ensure that the result is still an ideal family, we add \( \text{ground} \setminus \{v\} \) as a hyperedge if it is missing.  
In the case of an ideal Ffamily, deletion differs from the general deletion operation on set families in that the ground set is explicitly preserved after the operation.

The following is the relation between deletion to set family and deletion as an ideal family when the family does not have \( \text{ground} \setminus \{v\} \). \( \text{F.deletion} \) represents the deletion as an ideal family and \( \text{F.toSetFamily.deletion'} \) represents the usual deletion for a set family.

```lean
lemma ideal_deletion_noneuv_num (F : IdealFamily α)[DecidablePred F.sets] (x : α)(hx:x ∈ F.ground)(ground_ge_two: F.ground.card ≥ 2) (h_uv_none : ¬(F.sets (F.ground \ {x})))
  [DecidablePred (F.deletion x hx ground_ge_two).sets][DecidablePred (F.toSetFamily.deletion' x hx ground_ge_two).sets]:
  (F.deletion x hx ground_ge_two).number_of_hyperedges = (F.toSetFamily.deletion' x hx ground_ge_two).number_of_hyperedges + 1 :=

lemma ideal_deletion_noneuv_total (F : IdealFamily α) [DecidablePred F.sets](x : α)(hx:x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) (h_uv_none : ¬(F.sets (F.ground \ {x})))
  [DecidablePred (F.deletion x hx ground_ge_two).sets][DecidablePred (F.toSetFamily.deletion' x hx ground_ge_two).sets]:
  (F.deletion x hx ground_ge_two).total_size_of_hyperedges = (F.toSetFamily.deletion' x hx ground_ge_two).total_size_of_hyperedges + (F.ground.card - 1) :=
```

### **Trace**
For a set family, the trace with respect to a vertex \( v \) is defined as the set family obtained by taking all hyperedges \( H \) and replacing them with \( H \setminus \{v\} \). The trace of an ideal family is also an ideal family.  
Since traces in this context appear only for vertices with degree 1, the trace operation for an ideal family coincides with deletion. Therefore, in proofs, we avoid explicitly defining the trace and instead use the deletion operation on ideal families as a substitute.

## Outline of the Proof of the Theorem

The main theorem of this study (stated as `theorem ideal_average_rarity` in `FranklMain.lean`) asserts that ideal families are always rare on average. Below is an outline of the proof.

The proof is primarily based on induction on the size of the ground set.

### **Base Case**
For the base case \( n = 1 \), the claim is proven as `theorem nds_nonposi_card_one`.

### **Inductive Step**
In the inductive step, we assume the statement holds for ideal families with a ground set of size \( n \). Under this assumption, we prove the statement for ideal families with a ground set of size \( n + 1 \). Specifically, we need to show that the **normalized degree sum**: \( 2 \times \text{(sum of hyperedge sizes)} - \text{(size of the ground set)} \times \text{(number of hyperedges)} \)) is negative.

#### **Finding a Rare Vertex**
We begin by proving that the Ideal Family has a rare vertex, which is stated in `FranklRare.lean` as `theorem ideal_version_of_frankl_conjecture`. Let this rare vertex be \( v \).

#### **Handling Contraction and Deletion**
The family obtained by contracting the ideal family by a vertex \( v \) is also an ideal family. However, if \(\{v\}\) is not a hyperedge, the contracted family does not include the empty set, requiring a case distinction based on whether \(\{v\}\) is a hyperedge.

Similarly, the family obtained by deleting \( v \) from an ideal family is also an ideal family. However, if \(\text{ground} \setminus \{v\}\) is not a hyperedge, the deletion removes the ground set. Thus, we consider a deletion operation that explicitly adds back \(\text{ground} \setminus \{v\}\) when needed to ensure the result remains an ideal family.

#### **Four Cases**
We divide the proof into four cases based on whether \(\text{ground} \setminus \{v\}\) is a hyperedge and whether \(\{v\}\) is a hyperedge. These cases are handled as follows:
- `case_hs_haveUV`: Both \(\text{ground} \setminus \{v\}\) and \(\{v\}\) are hyperedges.
- `case_hs_noneUV`: \(\{v\}\) is a hyperedge, and \(\text{ground} \setminus \{v\}\) is not a hyperedge.
- `case_degone_haveUV`: \(\{v\}\) is not a hyperedge, and \(\text{ground} \setminus \{v\}\) is a hyperedge.
- `case_degone_noneUV`: Neither \(\text{ground} \setminus \{v\}\) nor \(\{v\}\) are hyperedges.

For each case, the number of hyperedges and the total size of hyperedges are expressed in terms of the corresponding values for the families obtained by deleting or contracting \( v \).

#### **Special Case: Degree-One Vertex**
If \(\{v\}\) is not a hyperedge, the degree of \( v \) is 1. In this scenario, instead of contraction, we consider the trace of \( v \), which results in another ideal family. When the degree of \( v \) is 1, tracing \( v \) is equivalent to the specialized deletion operation for ideal families.

## Lemma for each case when {v} is a hyperedge

### Lemma about number of hyperedges

When \(\{v\}\) is a hyperedge, the calculation of the number of hyperedges is appeared in `FrankNDS.lean'

```lean
lemma number_have (F: IdealFamily α) [DecidablePred F.sets] (v:α) (geq2: F.ground.card ≥ 2) (vin: v ∈ F.ground)(hs: F.sets {v})
  [DecidablePred (F.toSetFamily.deletion' v vin geq2).sets] [DecidablePred (F.contraction v hs geq2).sets]:
F.number_of_hyperedges = (F.toSetFamily.deletion' v vin geq2).number_of_hyperedges + (F.contraction v hs geq2).number_of_hyperedges :=
```

### Lemma about total sum of hyperedge size

```lean
lemma total_have{α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets] (singleton_have :F.sets {x}) :
  F.total_size_of_hyperedges = (F.deletion x hx geq2).total_size_of_hyperedges + (F.contraction x hx geq2).total_size_of_hyperedges +  F.degree x:=
```

### Lemma abount normalized degree sum 

the relation of normalized degree sum to those of minors.

```lean
theorem nds_set_minors (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
 (hs : F.sets {x}):
  F.toSetFamily.normalized_degree_sum =
  (F.toSetFamily.deletion' x hx geq2).normalized_degree_sum +
  (F.toSetFamily.contraction x hx geq2).normalized_degree_sum
  +2*(F.degree x) - F.number_of_hyperedges :=
```

### Lemma about normalized degree sum when ground \ {v} is not hyperedges

the relation of normalized degree sum between deletion for set family and the deletion as an ideal family.

```lean
lemma nds_deletion_noneuv (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets](hx_hyperedge : ¬F.sets (F.ground \ {x})) :
  (F.deletion x hx geq2).normalized_degree_sum = (F.toSetFamily.deletion' x hx geq2).normalized_degree_sum + Int.ofNat F.ground.card - 1:=
```

## Case when {v} is not a hyperedge

In an ideal family where \(\{v\}\) is not a hyperedge, the degree of \(v\) is 1. In this case, the set family obtained by tracing \(v\) can be shown to be an ideal family.

The relationship between the number of hyperedges in the original family and the traced family can be calculated separately for the cases where \(\text{ground} \setminus \{v\}\) is a hyperedge and where it is not. Similarly, the relationship between the sum of hyperedge sizes in the original family and in the traced family can also be determined for both cases.

When \(\text{ground} \setminus \{v\}\) is a hyperedge and \(\{v\}\) is not, the ideal family is determined entirely by the size of the ground set (\(n\)). In this case, the normalized degree sum can be directly computed, and it can be confirmed to be non-positive. This analysis is implemented in `IdealDegreeOne.lean`.

For the case where neither \(\{v\}\) nor \(\text{ground} \setminus \{v\}\) are hyperedges, the discussion is carried out in `IdealDegOneMain.lean`. Here, the traced family retains the same number of hyperedges as the original family, but the total size of the hyperedges is reduced by 1 compared to the original family. Using the inductive hypothesis, the non-positivity of the normalized degree sum for the traced family implies that the normalized degree sum for the original family is also non-positive.

# File descriptions

The Lean files are located in the Frankl folder of this repository.

- **FranklMain.lean**: Main theorem.
- **BasicDefinitions.lean**: Basic definitions.
- **BasicLemmas.lean**: Basic lemmas.
- **FamilyLemma.lean**: Lemmas about set families.
- **FranklMinors.lean**: Definitions and lemmas related to minors.
- **FranklNDS.lean**: Case where \(\{v\}\) is a hyperedge.
- **DegreeOneHave.lean**: Case where \(\{v\}\) is not a hyperedge, but \(\text{ground} \setminus \{v\}\) is a hyperedge.
- **DegreeOneNone.lean**: Case where neither \(\{v\}\) nor \(\text{ground} \setminus \{v\}\) are hyperedges.
- **FranklRare.lean**: Proof that Ideal Families have a rare vertex.
- **OtherTheorem.lean**: Theorems not used in the proof of the main theorem. 
1. Ideal families are closed under intersection.
2. Being rare on average implies the existence of a rare vertex.
3. In the frankl's conjecture, the equivalence between the assumption that the cardinality of members is at least two and the existence of the ground set as a hyperedge.

# Lean Environment

The version of Lean used is `leanprover/lean4:v4.17.0`.  
This version was selected because it supports Lean Copilot, which was utilized during the proof development. The `lakefile.lean` is configured to ensure that Lean Copilot is downloaded, and the imports explicitly include Lean Copilot. Be cautious when using this project in environments where Lean Copilot is not supported.

You can clone the repository locally with the following command:
```bash
git clone https://github.com/kashiwabarakenji/frankl_lean.git
```
If you already have Lean installed via elan, you can set up the project as follows:

```bash
cd frankl_lean
elan override set leanprover/lean4:v4.17.0
lake update
lake build
```

Once this is done, open the frankl_lean folder in Visual Studio Code with the Lean 4 extension installed. Press the "Start Lean Server" button in the editor as needed to begin working with Lean in the project.
