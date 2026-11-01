/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace HtmlModel.Svg

inductive Elem where
  | a | animate | animateMotion | animateTransform | circle | clipPath | defs | desc | discard
  | ellipse
  | feBlend | feColorMatrix | feComponentTransfer | feComposite | feConvolveMatrix
  | feDiffuseLighting | feDisplacementMap | feDistantLight | feDropShadow | feFlood | feFuncA
  | feFuncB | feFuncG | feFuncR | feGaussianBlur | feImage | feMerge | feMergeNode | feMorphology
  | feOffset | fePointLight | feSpecularLighting | feSpotLight | feTile | feTurbulence | filter
  | foreignObject | g | image | line | linearGradient | marker | mask | metadata | mpath | path
  | pattern | polygon | polyline | radialGradient | rect | script | «set» | stop | style | svg
  | switch | symbol | text | textPath | title | tspan | use | view
  deriving DecidableEq, Repr

def Elem.all : List Elem :=
  [.a, .animate, .animateMotion, .animateTransform, .circle, .clipPath, .defs, .desc, .discard,
    .ellipse,
    .feBlend, .feColorMatrix, .feComponentTransfer, .feComposite, .feConvolveMatrix,
    .feDiffuseLighting, .feDisplacementMap, .feDistantLight, .feDropShadow, .feFlood, .feFuncA,
    .feFuncB, .feFuncG, .feFuncR, .feGaussianBlur, .feImage, .feMerge, .feMergeNode, .feMorphology,
    .feOffset, .fePointLight, .feSpecularLighting, .feSpotLight, .feTile, .feTurbulence, .filter,
    .foreignObject, .g, .image, .line, .linearGradient, .marker, .mask, .metadata, .mpath, .path,
    .pattern, .polygon, .polyline, .radialGradient, .rect, .script, .set, .stop, .style, .svg,
    .switch, .symbol, .text, .textPath, .title, .tspan, .use, .view]

def Elem.name : Elem → String
  | .a => "a" | .animate => "animate" | .animateMotion => "animateMotion"
  | .animateTransform => "animateTransform" | .circle => "circle" | .clipPath => "clipPath"
  | .defs => "defs" | .desc => "desc" | .discard => "discard" | .ellipse => "ellipse"
  | .feBlend => "feBlend"
  | .feColorMatrix => "feColorMatrix" | .feComponentTransfer => "feComponentTransfer"
  | .feComposite => "feComposite" | .feConvolveMatrix => "feConvolveMatrix"
  | .feDiffuseLighting => "feDiffuseLighting" | .feDisplacementMap => "feDisplacementMap"
  | .feDistantLight => "feDistantLight" | .feDropShadow => "feDropShadow" | .feFlood => "feFlood"
  | .feFuncA => "feFuncA" | .feFuncB => "feFuncB" | .feFuncG => "feFuncG" | .feFuncR => "feFuncR"
  | .feGaussianBlur => "feGaussianBlur" | .feImage => "feImage" | .feMerge => "feMerge"
  | .feMergeNode => "feMergeNode" | .feMorphology => "feMorphology" | .feOffset => "feOffset"
  | .fePointLight => "fePointLight" | .feSpecularLighting => "feSpecularLighting"
  | .feSpotLight => "feSpotLight" | .feTile => "feTile" | .feTurbulence => "feTurbulence"
  | .filter => "filter" | .foreignObject => "foreignObject" | .g => "g" | .image => "image"
  | .line => "line" | .linearGradient => "linearGradient" | .marker => "marker" | .mask => "mask"
  | .metadata => "metadata" | .mpath => "mpath" | .path => "path" | .pattern => "pattern"
  | .polygon => "polygon" | .polyline => "polyline" | .radialGradient => "radialGradient"
  | .rect => "rect" | .script => "script" | .set => "set" | .stop => "stop" | .style => "style"
  | .svg => "svg" | .switch => "switch" | .symbol => "symbol" | .text => "text"
  | .textPath => "textPath" | .title => "title" | .tspan => "tspan" | .use => "use"
  | .view => "view"

def Elem.ofName? (name : String) : Option Elem := Elem.all.find? (·.name == name)

/-- The named categories that content models list. -/
inductive Group where
  | animation | descriptive | paintServer | gradient | shape | structural | textContentChild
  | filterPrimitive | transferFunction | lightSource
  deriving DecidableEq, Repr

def Elem.groups : Elem → List Group
  | .animate | .animateMotion | .animateTransform | .discard | .set => [.animation]
  | .desc | .title | .metadata => [.descriptive]
  | .linearGradient | .radialGradient => [.gradient, .paintServer]
  | .pattern => [.paintServer]
  | .circle | .ellipse | .line | .path | .polygon | .polyline | .rect => [.shape]
  | .defs | .g | .svg | .symbol | .use => [.structural]
  | .tspan | .textPath => [.textContentChild]
  | .feBlend | .feColorMatrix | .feComponentTransfer | .feComposite | .feConvolveMatrix
  | .feDiffuseLighting | .feDisplacementMap | .feDropShadow | .feFlood | .feGaussianBlur
  | .feImage | .feMerge | .feMorphology | .feOffset | .feSpecularLighting | .feTile
  | .feTurbulence => [.filterPrimitive]
  | .feFuncA | .feFuncB | .feFuncG | .feFuncR => [.transferFunction]
  | .feDistantLight | .fePointLight | .feSpotLight => [.lightSource]
  | _ => []

def Group.all : List Group :=
  [.animation, .descriptive, .paintServer, .gradient, .shape, .structural, .textContentChild,
    .filterPrimitive, .transferFunction, .lightSource]

/-- The distinct lists of children that content models admit in any number and order. The `a`
variants are those within an `a`, which may not hold another. -/
inductive Model where
  | container | aContainer | text | aText | tspan | aTspan | textPath | aTextPath | clipPath | use
  | switch | shape | gradient | stop | view
  /-- What animation elements, `mpath`, and lighting filter primitives hold besides their one
  required or optional child: descriptive elements and `script`. -/
  | animation
  | filter | componentTransfer | merge | feImage | primitive
  deriving DecidableEq, Repr

def Model.all : List Model :=
  [.container, .aContainer, .text, .aText, .tspan, .aTspan, .textPath, .aTextPath, .clipPath, .use,
    .switch, .shape, .gradient, .stop, .view, .animation, .filter, .componentTransfer, .merge,
    .feImage, .primitive]

/-- Content models list both named categories and single elements, so each element is a category
of its own, which widens to the named categories it belongs to, and to the content of each model
that lists it or one of them. -/
inductive Cat where
  | el (e : Elem)
  | group (g : Group)
  /-- `a` holds what its parent holds, so it takes one category for each distinct content model
  of the parents that admit it. -/
  | aContainer | aText | aTspan | aTextPath
  | content (m : Model)
  deriving DecidableEq, Repr

def Cat.all : List Cat :=
  Elem.all.map .el ++ Group.all.map .group ++ [.aContainer, .aText, .aTspan, .aTextPath] ++
    Model.all.map .content

theorem Cat.mem_all (c : Cat) : c ∈ Cat.all := by
  cases c with
  | el e => cases e <;> decide
  | group g => cases g <;> decide
  | content m => cases m <;> decide
  | _ => decide

/-- Every named category `c` belongs to, transitively. -/
def Cat.above : Cat → List Cat
  | .el e => e.groups.map .group
  | .group .gradient => [.group .paintServer]
  | _ => []

/-- Whether an `a` stands among text, where whitespace renders. -/
def Cat.inText : Cat → Bool
  | .aText | .aTspan | .aTextPath => true
  | _ => false

def Elem.cats : Elem → List Cat
  | .a => [.aContainer, .aText, .aTspan, .aTextPath]
  | e => [.el e]

/-- Elements within which whitespace renders as text, so that a pretty-printer may add none. -/
def Elem.keepsWhitespace : Elem → Bool
  | .text | .tspan | .textPath => true
  | _ => false

end HtmlModel.Svg
