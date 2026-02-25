Content-Length: 247

{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"processId":null,"clientInfo":{"name":"manual-script","version":"0.1"},"rootUri":"file:///home/awaldis/repos/linear-algebra-done-right","capabilities":{},"trace":"off","workspaceFolders":[]}}
Content-Length: 52

{"jsonrpc":"2.0","method":"initialized","params":{}}
Content-Length: 1319

{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///home/awaldis/repos/linear-algebra-done-right/LinearAlgebraDoneRight/TinyProofs.lean","languageId":"lean","version":1,"text":"/-!\n# Tiny Lean Proofs\n\nExamples of the smallest possible proofs in Lean 4.  Each lemma is chosen so\nthat the kernel can validate it with a single primitive rule such as `rfl`\n(reflexivity), direct projection, or immediate constructor introduction.\n-/\n\ntheorem true_is_true : True :=\n  True.intro\n\n/-- Reflexivity (`rfl`) is the simplest proof: any term is definitionally equal to itself. -/\ntheorem refl_example (α : Sort _) (x : α) : x = x :=\n  rfl\n\n/-- Identity functions can be proven with a single lambda that hands the input back. -/\ntheorem id_preserves (P : Prop) : P → P :=\n  fun h => h\n\n/-- Conjunction projections reduce to retrieving `.left` or `.right` from the proof pair. -/\ntheorem and_right {P Q : Prop} : P ∧ Q → Q :=\n  fun h => h.right\n\n/-- Numerals are definitionally equal to themselves; no arithmetic reasoning is needed. -/\ntheorem zero_eq_zero : (0 : Nat) = 0 :=\n  rfl\n\n/-- `Eq.refl` can be chained by function application; the kernel does not need rewriting here. -/\ntheorem apply_id {α : Sort _} (x : α) : (fun y => y) x = x :=\n  rfl\n"}}}
Content-Length: 220

{"jsonrpc":"2.0","id":1,"method":"textDocument/hover","params":{"textDocument":{"uri":"file:///home/awaldis/repos/linear-algebra-done-right/LinearAlgebraDoneRight/TinyProofs.lean"},"position":{"line":10,"character":10}}}
Content-Length: 58

{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}
Content-Length: 33

{"jsonrpc":"2.0","method":"exit"}
