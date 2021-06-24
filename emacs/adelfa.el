;; Emacs mode for Adelfa theorem files.
;;

(defvar adelfa-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.ath\\'" . adelfa-mode))

(defun make-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)\\>"))

(defun make-command-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)[^.]*."))

;; (require 'font-lock)
;; (defvar adelfa-font-lock-keywords
;;   (list
;;     (cons (make-command-regex "Set" "Query") font-lock-type-face)
;;     (cons (make-regex "Import" "Specification") font-lock-variable-name-face)
;;     (cons (make-command-regex "Type" "Kind" "Close") font-lock-keyword-face)
;;     (cons (make-command-regex "Define" "CoDefine") font-lock-keyword-face)
;;     (cons (make-command-regex "Theorem" "Split") font-lock-function-name-face)
;;     (cons (make-regex "skip") font-lock-warning-face))
;;   "Default highlighting for Adelfa major mode")

;; (setq xemacsp (and (boundp 'xemacsp) xemacsp))

;; (defvar adelfa-mode-syntax-table
;;   (let ((adelfa-mode-syntax-table (make-syntax-table)))
;;     (modify-syntax-entry ?_ "w"     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?' "w"     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?/ (if xemacsp "w 14" "w 14n")
;;                          adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?* (if xemacsp ". 23" ". 23n")
;;                          adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?% "< b"   adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?\n "> b"  adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?. "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?+ "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?- "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?= "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?> "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?< "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?# "."     adelfa-mode-syntax-table)
;;     (modify-syntax-entry ?\ "."     adelfa-mode-syntax-table)
;;     adelfa-mode-syntax-table)
;;   "Syntax table for Adelfa major mode")

;; Proof navigation
(defvar adelfa-mode-keymap
  (let ((adelfa-mode-keymap (make-keymap)))
    (define-key adelfa-mode-keymap "\C-c\C-e" 'adelfa-previous-command-send)
    (define-key adelfa-mode-keymap "\C-c\C-n" 'adelfa-forward-command-send)
    (define-key adelfa-mode-keymap "\C-c\C-p" 'adelfa-backward-command-send)
    adelfa-mode-keymap)
  "Keymap for Adelfa major mode")

(defun adelfa-forward-command ()
  (interactive)
  (search-forward-regexp "%\\|\\(\\(Specification\\ \".*\"\\.\\)\\|\\.\\)")
  (if (equal (match-string 0) "%")
      (progn (beginning-of-line)
             (next-line 1)
             (adelfa-forward-command))))


(defun adelfa-backward-command ()
  (interactive)
  (backward-char 1)
  (adelfa-backward-command-rec)
  (if (not (bobp))
    (forward-char 1)))

(defun adelfa-backward-command-rec ()
  (interactive)
  (while (search-backward "%" (point-at-bol) t))
  (if (not (search-backward "." (point-at-bol) t))
      (progn
        (beginning-of-line 1)
        (if (not (bobp))
            (progn (end-of-line 0)
                   (adelfa-backward-command-rec))))))

(defun adelfa-previous-command-send ()
  (interactive)
  (adelfa-backward-command)
  (adelfa-forward-command-send))

(defun adelfa-forward-command-send ()
  (interactive)
  (let ((beg (point))
        str)
    (adelfa-forward-command)
    (setq str (buffer-substring beg (point)))
    (other-window 1)
    (switch-to-buffer "*shell*")
    (end-of-buffer)
    (insert str)
    (comint-send-input)
    (other-window -1)))

(defun adelfa-backward-command-send ()
  (interactive)
  (adelfa-backward-command)
  (other-window 1)
  (switch-to-buffer "*shell*")
  (end-of-buffer)
  (insert "undo.")
  (comint-send-input)
  (other-window -1))

(defun adelfa-mode ()
  "Major mode for editing Adelfa theorem files"
  (interactive)
  (kill-all-local-variables)
  ;; (set-syntax-table adelfa-mode-syntax-table)
  (use-local-map adelfa-mode-keymap)
  ;; (set (make-local-variable 'font-lock-defaults)
  ;;      '(adelfa-font-lock-keywords))
  (set (make-local-variable 'comment-start) "%")
;  (set (make-local-variable 'indent-line-function) 'adelfa-indent-line)
  (setq major-mode 'adelfa-mode)
  (setq mode-name "Adelfa")
  (run-hooks 'adelfa-mode-hook))

(provide 'adelfa-mode)
