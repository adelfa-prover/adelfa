# Adelfa Proof General

## Installation

Copy the `adelfa` directory as a whole from this repo and paste it into your
install of Proof General. Then add an entry for Adelfa resembling: `(adelfa
"Adelfa" "ath")` in the `proof-assistant-table-default` constant, located in
`PG/generic/proof-site.el`, like:

``` emacs-lisp
(defconst proof-assistant-table-default
    '(
      ;; Main instances of PG.

      (isar "Isabelle" "thy")
      (coq "Coq" "v" nil (".vo" ".glob"))
      (easycrypt "EasyCrypt" "ec" "\\.eca?\\'")
      (phox "PhoX" "phx" nil (".phi" ".pho"))
      (adelfa "Adelfa" "ath")
```

Your personal configuration for Proof General should still work. If it does
not, ensure your byte compilations are up to date or don't compile it at all.
Here is my configuration for reference:

``` emacs-lisp
(defconst proof-site-file
  (expand-file-name "path-to-pg/PG/generic/proof-site.el"))

(setq proof-splash-enable nil
      proof-output-tooltips nil
      proof-three-window-mode-policy 'horizontal)
(add-hook 'adelfa-mode-hook
          #'(lambda ()
              (setq indent-line-function 'indent-relative)))

(load-file proof-site-file)
(setq auto-mode-alist
   (append
     '(("\\.ath\\'" . adelfa-mode))
     auto-mode-alist))
```

## Important Notes

Adelfa compatibility with Proof General is still in its infancy. It should work
for many common workflows, but it may become out of sync at times. This happens
when an error occurs in Adelfa that is not recognized as such by Proof General.
When this happens, abort the proof with `C-c C-x` and continue the proof up to
the unrecognized error. Even better, consider [creating an
issue](https://github.com/CJohnson19/PG/issues/new) with what Adelfa responded
with.

Adelfa doesn't have a notion of undoing a completed proof. Therefore, if you
want to add content above a completed proof, Proof General can become confused,
and you should restart to sync the state again.
