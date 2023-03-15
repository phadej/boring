# Revision history for boring

## 0.2.1

-  Add instances for `SNat`, `SSymbol`, and `SChar`
   (singletons introduced in `base-4.18.0.0`)

## 0.2

- Make `boring` package dependency light.
  `fin`, `bin`, `ral`, `vec`, `dec`, `singleton-bool` instances
  are migrated to corresponding packages.
  Rest are migrated to `boring-instances` for now.
- Data.Boring is `Trustworthy`
- Add Generic derivation. Thanks to David Feuer.

## 0.1.3

- Allow `vec-0.3`
- Add instances for `ral` and `bin` types.

## 0.1.2

- Add instances for 'Boring' instances for 'SBool', 'SNat' and 'LE'.
- Add 'Boring (Dec a)', 'boringYes' and 'boringNo'.

## 0.1.1

- Add `GHC.Generics` instances
- Add `:~~:` and `Coercion` instances

## 0.1

- `streams`, `constraints`, `generics-sop` instances.
- Reversed dependency with `vec`, add `fin` instances.

## 0

- First version. Released on an unsuspecting world.
