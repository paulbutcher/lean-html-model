/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace HtmlModel

/-- What a markup macro builds an element's payload with. Each attribute is applied in the
order written, to the payload built from those before it, so that an instance can make the last
occurrence of a name win. -/
class HtmlPayload (P : Type) where
  empty : P
  attr : String → String → P → P
  /-- A boolean attribute: present when `true`, absent when `false`. -/
  flag : String → Bool → P → P
  /-- One inline style property. -/
  style : String → String → P → P
  /-- The element's identity among its siblings, for a renderer that diffs. -/
  key : String → P → P
  /-- Attributes spliced in, which override those before them. -/
  append : P → P → P

/-- An event attribute, such as `onClick`, on payload `P`. `event` is the attribute's name as
written, so that an instance can give `onEnter` a meaning no DOM event has. -/
class EventAttr (P : Type) (event : String) (α : outParam Type) where
  on : α → P → P

end HtmlModel
