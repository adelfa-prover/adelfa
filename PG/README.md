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

In your Emacs configuration, commonly located at `~/.emacs` or
`~/.emacs.d/init.el`, add the following lines: 

``` emacs-lisp
(defconst proof-site-file
  (expand-file-name "path-to-pg/PG/generic/proof-site.el"))

(when (file-exists-p proof-site-file)
  (setq proof-splash-enable nil
        proof-output-tooltips nil
        proof-three-window-mode-policy 'horizontal)

  (load-file proof-site-file)

  (add-hook 'adelfa-mode-hook
            #'(lambda ()
                (setq indent-line-function 'indent-relative)))

  (setq auto-mode-alist
        (append
         '(("\\.ath\\'" . adelfa-mode))
         auto-mode-alist)))
```

Where `path-to-pg` should be changed to the file path of your installation
location of Proof General.

If you have previously installed Proof General and it seems Adelfa isn't
working, the byte compilation of your installation may be out of date. Running
the `make` command in the `PG` directory should refresh them. You may also wish
to not byte compile PG by running `make clean`.

## Using Proof General

You can now use Emacs to open a `ath` file. After executing your first command
you should see two new windows representing the assistant's state. Some
basic and common Proof General commands are:

- `C-c C-RET` Execute command(s) up to the pointer position.
- `C-c C-n` Execute next command.
- `C-c C-u` Undo last command.

Where then `C-c C-n` notation represents control key with "c" followed by
control key with "n".

More in depth instructions can be found in the [Proof General User
Documentation](https://proofgeneral.github.io/doc/master/userman/).

## Important Notes

Adelfa compatibility with Proof General is still in its infancy. It should work
for many common workflows, but it may become out of sync at times. This happens
when an error occurs in Adelfa that is not recognized as such by Proof General.
When this happens, abort the proof with `C-c C-x` and continue the proof up to
the unrecognized error. Consider [emailing the
maintainer](mailto:joh13266@umn.edu) with a description of the error.
