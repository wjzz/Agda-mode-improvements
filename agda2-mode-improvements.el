;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Agda-mode improvements definitions start here

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; [] A few utility functions


(defun agda2-list-to-string-with-sep (l &optional sep)
  "An invert to split-sting. Joins a list of strings with a single space or
a custom separator sep, if given."
  (unless sep
    (setf sep " "))
  (if l
      (apply 'concat (first l) (mapcar (lambda (s) (concat sep s))
                                       (rest l)))
      ""))

; (agda2-split-names (list "hello" "t-" "-t" "10"))


;; extracted from agda2-goal-cmd
(defun agda2-read-txt-from-goal ()
  "Returns the text inputed in the current goal."
  (lexical-let ((o (first (agda2-goal-at (point)))))
    (buffer-substring-no-properties (+ (overlay-start o) 2)
                                    (- (overlay-end   o) 2))))


;; copied from slime.el, previously called slime-trim-whitespace
(defun agda2-trim-whitespace (str)
  (save-match-data
    (string-match "^\\s-*\\(.*?\\)\\s-*$" str)
    (match-string 1 str)))

(defun agda2-extract-indentation (str)
  "Extracts the indentation prefix of str."
  (save-match-data
    (string-match "^\\(\\s-*\\).*?" str)
    (match-string 1 str)))

;; example
;; (agda2-extract-indentation "  hello!")    
;; "  "

(defun agda2-join-dbs-as-hash (all-dbs)
  "Takes a list of lists and inserts them into a hash
with the key being the first element of each list. Empty lists
are ignored."
  (lexical-let 
      ((hash (make-hash-table :test 'equal)))
    (dolist (db all-dbs hash)
      (when db
        (lexical-let 
            ((db-name (first db))
             (lemmas  (rest db)))
          (puthash db-name 
                   (append (gethash db-name hash)
                           lemmas) 
                   hash))))))

(defun agda2-hash-to-list (hash)
  "Convert a hash to list of lists where first/car is the key
and rest/cdr is the value."
  (lexical-let (result)
    (maphash (lambda (k v) (push (list k v) result)) hash)
    result))

; (agda2-hash-to-list (agda2-join-dbs-as-hash '(("global" "hello") ("arith" "plus") ("global" "hello2"))))
; yields
; (("arith" ("plus")) ("global" ("hello" "hello2")))

(defun agda2-pretty-print-db-list (lists)
  (lexical-let 
      (elements)
    (dolist (l lists)
      (push (concat (first l) ":\n\t" (agda2-list-to-string-with-sep (second l))) elements))
    (agda2-list-to-string-with-sep (reverse elements) "\n")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; [] Hint databases for auto/agsy

(defun agda2-extract-dbs-from-file (module-name)
  (save-excursion
    (lexical-let ((import-prefix "import "))
      (goto-char (point-min))
      (re-search-forward (concat import-prefix module-name))
      (backward-char 2)
      (agda2-goto-definition-keyboard)
      (goto-char (point-max))
      (lexical-let 
          ((extraction (agda2-extract-dbs-from-buffer)))
        (kill-buffer)
        extraction))))
        
(defun agda2-partition-into-part (parts)
  (lexical-let
      ((to-first t)
       bases
       into)
    (dolist (part parts (list (reverse bases) 
                              (reverse into)))
      (cond ((string-equal "INTO" part)  ;; from now on add to the into list
             (setq to-first nil))
            (to-first
             (push part bases))
            (t
             (push part into))))))

; (agda2-partition-into-part '("heloo" "lem" "tralala"))
; (agda2-partition-into-part '("heloo" "lem" "tralala" "INTO" "arith"))
              

(defun agda2-filter-imports (imported-data chosen-db-names)
  (lexical-let
      (results)
    (dolist (decl imported-data (reverse results))
      (if (and decl
               (member (first decl) chosen-db-names))
          (push decl results)))))

; (agda2-filter-imports '(("global" "lem") ("arith" "jam")) '("arith"))

(defun agda2-rename-imports (imported-data new-name)
  (mapcar (lambda (l) (if l
                          (cons new-name (rest l))
                          l))
          imported-data))

; (agda2-rename-imports '(("global" "lem") ("arith" "jam")) "imported-db")

(defun agda2-extract-dbs-from-buffer ()
  "Travels the whole buffer and looks for db declarations.
A db declaration is a comment of form 
{- BASE name-of-db theorem-name* -}
db declaration can mention the same database multiple times in a file
and all listed theorems will be merged and included in the result.
This function, however, does not perform the merging."
  (interactive)
  (lexical-let 
      ((end-boundary (point))
       start end results)
    (save-excursion
      (goto-char (point-min))
      (while (setq start 
                   (re-search-forward "{- BASE" end-boundary t))
        (when (re-search-forward "-}" end-boundary t)
          (setq end (match-beginning 0))
          (decf end)
          (lexical-let*
              ((parts (split-string (buffer-substring-no-properties start end))))
            (if (string-equal "IMPORT" (first parts))

                ;; we need to import declarations
                (lexical-let*
                    ((imported-data (agda2-extract-dbs-from-file (second parts)))
                     (partitioned   (agda2-partition-into-part (rest (rest parts))))
                     (bases         (first partitioned))
                     (renaming      (second partitioned))
                     (filtered-data (if bases 
                                        (agda2-filter-imports imported-data bases)
                                        imported-data))
                     (final-data    (if renaming
                                        (agda2-rename-imports filtered-data (first renaming))
                                        filtered-data)))
                  (setq results (append final-data results)))
                
                ;; we don't need to import declarations
                (push parts results)))))
      results)))

(defun agda2-get-db-contents-many (db-names all-dbs)
  "Iterates through the all-dbs list and collects the theorems
from all databases with their names in the db-names list.

db-names should be a list of strings ;
all-dbs should be a list of list of strings, where
the first element of each list is the name of db and
the rest are the names of the theorems included in the given db."
  (lexical-let (results)
    (dolist (db all-dbs results)
      (when (and db
                 (member-if (lambda (db-name)
                              (string-equal db-name 
                                            (first db)))
                            db-names))
        (setq results (append (rest db)
                              results))))))

        ;; the order of arguments of the append above
        ;; determines the order in which the lemmas
        ;; from a given db will be tried.
        ;; Please we bear in mind, that since we parse the file
        ;; and push the db declarations onto a stack and do no
        ;; reverse it in the end, the order is actually twisted :->
        ;; * (append (rest db) results)
        ;;   this way the oldest declarations (closer to the top of the file)
        ;;   will be used first
        ;; * (append results (rest db))
        ;;  this will make auto try the latests declaration
        ;;  go first. Actually, (append results (reverse (rest db)))
        ;;  would precisely simulate a real LIFO behavior.

        ;; switching to the LIFO version has the nice feature,
        ;; that the last added theorem should be more useful
        ;; than the first one (or otherwise why add the last theorem
        ;; in the first place [pardon the pun]).

                              
(defun agda2-split-names (names)
  "Given a list of strings (the current goal's input splitted)
partitions it into two groups:
 1) options to auto (ie. -c -t 10 ...)
 2) names of databases
The result is given as list of length 2."

  ;; currently we pick everything that starts with
  ;; a '-' or digit to be an option
  ;; and anything else to be a db name
  ;; Is it good enough?
  (flet
      ((predicate (name) (string-match "^[-0-9]" name)))
           
    ;; split names into auto options and names of db's
    (list (remove-if-not 'predicate names)
          (remove-if     'predicate names))))


(defun agda2-build-hints ()
  "Searches the file for database declarations, read a list of chosen data-bases (and 
auto options, if given) from the current goal's input and returns a string
that is ready to be given to auto as hints."
  (lexical-let* 
      ((dbs      (agda2-extract-dbs-from-buffer))
       (goal-txt (agda2-read-txt-from-goal))
       (names    (split-string goal-txt))

       ;; split names into two groups: options and names of dbs
       (splitted     (agda2-split-names names))
       (auto-options (first splitted))
       (db-names     (or (second splitted)  ;; if second splitted is empty, 
                         (list "global")))  ;; use the global db
       
       (theorems (agda2-get-db-contents-many db-names dbs))
                                                      
       (hints    (agda2-list-to-string-with-sep (append auto-options
                                                        theorems))))
    hints))
  

;; need to make sure we're in a goal
(defun agda2-solve-with-db ()
  "Reads the name of the db from the current goal input field,
and calls auto with the theorems from the db as hints."
  (interactive)
  (multiple-value-bind (o g) (agda2-goal-at (point))
    (unless g (error "For this command, please place the cursor in a goal"))
    
    (lexical-let
        ((hints (agda2-build-hints)))

      ;; an ugly boundary case:
      ;;  if the cursor is at { in the goal, then insert will put the text before it,
      ;;  not after. So we have to move the cursor one position to the right
      (when (char-equal 123 ;; code of '{'
                        (char-before (+ 1 (point)))) ;; a strange way to extract the code of the
                                                     ;; current position
        (goto-char (+ 2 (point))))

      ;; make sure that the goal is empty
      (agda2-replace-goal (second (agda2-goal-at (point))) "")

      ;; intert the hints, just as if the user had inputted them by himself, and call auto
      (insert hints)
      (agda2-auto))))

(defun agda2-flatten-list (ls)
  (mapcar (lambda (l) (when l (cons (first l) (second l)))) ls))

(defun agda2-nested-string-list-quote (ls)
  (concat "[ " (agda2-list-to-string-with-sep (mapcar 'agda2-list-quote ls) ", ") " ] "))

(defun agda2-show-current-dbs (&optional verbose)
  "Prints a lists of dbs in the current scope and lists their contents.
If verbose is not nil, then each lemma is listed with it's type"
  (interactive "P")
  (lexical-let* 
      ((all-dbs (agda2-extract-dbs-from-buffer))
       (hash    (agda2-join-dbs-as-hash (reverse all-dbs)))
       (dbs     (agda2-hash-to-list hash)))
    (if verbose
        (lexical-let ((string-for-haskell (agda2-nested-string-list-quote (agda2-flatten-list dbs))))
          (agda2-go t nil (concat "cmd_infer_db_contents Agda.Interaction.BasicOps.Normalised " 
                                  (agda2-string-quote string-for-haskell))))
        (agda2-info-action "*DB contents* " (concat "\n" (agda2-pretty-print-db-list dbs))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; [] Adding a with expression to the current clause from a goal

;; Example:
;;   test m n = {! m == n ?}  -- type C-c C-w in goal
;;   ....

;;   test m n with m == n
;;   test m n | clause0 = {!!}
;;   ....
            

(defun agda2-generate-cond-str (var-name start count)
  "Generates a string to be inserted below the with expression.
Count in the number of clauses, start is the index of the first
variable.
For example:
 (agda2-generate-cond-str \"cond\" 0 4)
 yields
 ' | cond0 | cond1 | cond2 | cond3'"

  (lexical-let ((last-index (- (+ start count) 1)))
    (flet
        ;; this function is not tail-recursive,
        ;; but in practise we'll have only count < 10 (probably even < 5)
        ((iter (n)
               (if (> n last-index)
                   nil
                 (cons
                  (concat " | " var-name (int-to-string n)) 
                  (iter (+ 1 n))))))
      (apply 'concat (iter start)))))
    


(defun agda2-add-with-exp (&optional opt)
  "Inserts a with expression of the left hand side of an equation, if invoked in
a goal that is the right hand side of the equation. The contents of the goal
will be inserted as a argument of the with and an additional line with be inserted,
that will contain bidings for all expressions and a new goal after a '=' character.
The optional argument determines which variant should be used, see example:

Invoked with opt == nil in the goal below:
equal? m n = {! m \?= m !}
.....

will give
equal? m n with m \?= n
... | cond0 = {! !}
.....

 (with the cursor placed in the goal).

If opt is true then we'll get:

equal? m n with m \?= n
equal? m n | cond0 = {! cond0 !}
......
"
  (interactive "P")

  (multiple-value-bind (o g) (agda2-goal-at (point))
    (unless g (error "For this command, please place the cursor in a goal"))

    (lexical-let ((from-line-beg-to-point (buffer-substring-no-properties (line-beginning-position) 
                                                                  (point)))
          (goal-txt (agda2-trim-whitespace (agda2-read-txt-from-goal))))

      (unless (string-match " = " from-line-beg-to-point)
        (error "Can only add with expression to equations"))
      
      (when (string-match "\\`\\s *\\'" goal-txt)
        (setq goal-txt (read-string "Expression to with on: " nil nil goal-txt t)))

      (re-search-backward " = ")
      (lexical-let* ((lhs (buffer-substring-no-properties (line-beginning-position)
                                                  (point)))
             (indentation  (agda2-extract-indentation lhs))
             (no-of-bars-goal  (+ 1 (count 124 (string-to-list goal-txt))))
             (last-cond-index  (save-excursion
                                   (if (re-search-backward " cond\\([0-9]+\\)" (line-beginning-position) t)
                                       (string-to-number (match-string-no-properties 1))
                                     -1)))
             (no-of-bars-lhs   (+ 1 last-cond-index))
             (conds            (agda2-generate-cond-str "cond" no-of-bars-lhs no-of-bars-goal)))
        
        (kill-line)
        (insert " with " goal-txt)
        (newline)

        (if opt
            (insert lhs conds " = {!!}")
            (insert indentation "..." conds " = {!!}"))

        (agda2-load)
        (goto-char (- (point) 2))))))


;; this implementation makes one load too much
;; I'll leave it like this for a while,
;; if this proves to be annoying then I'll fix it.
(defun agda2-add-with-exp-make-case ()
  "Calls agda2-add-with-exp and then makes a case analysis on the
first clause."
  (interactive)
  (agda2-add-with-exp t)
  (insert "cond0")
  (agda2-make-case))  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; [] Generating a function stub with all arguments named

(defun agda2-generate-function-stub ()
"Generate a function stub from type declaration."
  (interactive)

  (end-of-line)
  (re-search-backward "^[^(]+: ")
  (re-search-forward " : ")
  (backward-char 3)
    
  (lexical-let* 
      ((name-end (point))
       (name (buffer-substring (line-beginning-position) (point))))
    (beginning-of-line)
    (while (not (looking-at "\\s *$"))
      (next-line)
      (beginning-of-line))
      (insert name)
      (insert " = ?")
      (agda2-load)

      (agda2-refine)

      (re-search-backward " = ")
      (re-search-forward " λ ")
      (delete-char -4)
      

      (re-search-forward "→")
      (delete-char -1)
      (insert "=")
      
      (agda2-load)
      (goto-char (+ 2 (point)))
      
      ;; insert an empty line below
      (setq back-point (point))
      (end-of-line)
      (newline)
      (goto-char back-point)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; [] Fix a line with broken patterns by inserting ... | 
(defun agda2-fix-line ()
  (interactive)

  ;; how many cases has the last with exp had?
  (setq no-of-bars (save-excursion
                     (re-search-backward " with ")
                     (+ 1 (count 124 (string-to-list (buffer-substring-no-properties (point) (line-end-position)))))))

  (beginning-of-line)
  (re-search-forward " = ")

  (while (> no-of-bars 0)
    (re-search-backward " | ")
    (decf no-of-bars))

  (lexical-let* 
      ((end-point (point))
       (upto-end (buffer-substring-no-properties (line-beginning-position) end-point))
       (indent   (agda2-extract-indentation upto-end)))
    (delete-region (line-beginning-position) end-point)
    (insert indent "...")))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Agda-mode improvements definitions end here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
