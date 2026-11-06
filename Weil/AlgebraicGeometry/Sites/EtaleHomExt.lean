module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Extensionality for morphisms of the small étale site

A morphism of the small étale site `X.Etale` of a scheme is determined by the underlying morphism
of schemes. This is `CategoryTheory.MorphismProperty.Over.Hom.ext` stated for
`AlgebraicGeometry.Scheme.Etale`, which is a `def` wrapping `CategoryTheory.MorphismProperty.Over`
and hence invisible to the `ext` tactic.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Etale

/-- A morphism of the small étale site of a scheme is determined by the underlying morphism of
schemes. -/
@[ext]
theorem hom_ext {X : Scheme.{u}} {V W : X.Etale} {f g : V ⟶ W} (h : f.left = g.left) : f = g :=
  MorphismProperty.Over.Hom.ext h

end AlgebraicGeometry.Scheme.Etale
