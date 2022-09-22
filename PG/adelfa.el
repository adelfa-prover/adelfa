;; adelfa.el ---- Proof General instance for Adelfa
;;
;; Copyright (C) 2021 Chase Johnson
;;
;; Authors: Chase Johnson <joh13266@umn.edu>
;;
;;; Commentary:
;;
;;
;;
;;; Code:

(eval-and-compile
  (require 'proof-site)
  (proof-ready-for-assistant 'adelfa))

(require 'proof)
(require 'proof-easy-config)
(require 'adelfa-syntax)

(defvar adelfa-shell-handle-output
  '(lambda (cmd string)
     (when (string-match "Proof \\(Completed!\\|Aborted\.\\)" string)
       (proof-clean-buffer proof-goals-buffer))))

;; (regexp-opt '("Error" "Typing error" "Syntax error"))

(defconst adelfa-error-terms-regexp
  "\\(?:\\(?:E\\|\\(?:Syntax\\|Typing\\) e\\)rror\\)"
  "Any error response that Adelfa may return to a command.")

(proof-easy-config
 'adelfa                                "Adelfa"
 proof-prog-name                        "adelfa"
 proof-terminal-string                  "."
 proof-script-comment-start-regexp      "%"
 proof-script-fly-past-comments         t
 proof-script-comment-end-regexp        "\n"
 proof-goal-command-regexp              proof-no-regexp
 proof-shell-proof-completed-regexp     proof-no-regexp
 proof-completed-proof-behaviour        'closeany
 proof-assistant-home-page              "http://sparrow.cs.umn.edu/adelfa/"
 proof-shell-annotated-prompt-regexp    "^.*>> $"
 proof-shell-quit-cmd                   "Quit."
 proof-shell-start-goals-regexp         "^Subgoal .*[^is]:$"
 proof-shell-end-goals-regexp           ">>"
 proof-shell-restart-cmd                "abort."
 proof-shell-error-regexp               adelfa-error-terms-regexp
 proof-shell-strip-crs-from-input       nil
 proof-save-command-regexp              proof-no-regexp
 proof-non-undoables-regexp             "\\(undo\\|redo\\|abort\\)"
 proof-find-and-forget-fn               'adelfa-find-and-forget-fn
 proof-script-syntax-table-entries      adelfa-mode-syntax-table-entries
 proof-script-font-lock-keywords        adelfa-script-font-lock-keywords
 proof-goals-font-lock-keywords         adelfa-goals-font-lock-keywords
 proof-response-font-lock-keywords      adelfa-response-font-lock-keywords
 proof-shell-handle-output-system-specific adelfa-shell-handle-output
 )

(provide 'adelfa)

(defun adelfa-find-and-forget-cmd (span)
  "Forgets a single Adelfa command represented by SPAN.

   If the command is a comment, we should take no action so as to maintain the
   correct state in our script. If the command is a theorem, we may undo it by
   aborting the proof. In the general case, we will simply tell Adelfa to undo."
  (setq cmd (span-property span 'cmd))
  (cond
   ((eq cmd nil) "") ; comment
   ((string-match ".*Theorem.*" cmd) "abort.") ; Theorem start
   (t "undo."))
  )

(defun adelfa-find-and-forget-fn (span)
  (setq ans ())
  (while span
    (setq typ (span-property span 'type))
    (if (not (eq typ 'comment))
        (let ((current-cmd (adelfa-find-and-forget-cmd span)))
          (setq ans (cons current-cmd ans))))
    (setq span (next-span span 'type)))
  ans)
;;; adelfa.el ends here
