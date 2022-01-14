# 写像
### 写像

\\( f(A \cup B) = f(A) \cup f(B) \\)
```
Lemma image_setU f A B : f @` (A `|` B) = f @` A `|` f @` B.
```

\\( f(A \cap B) \subset f(A) \cap f(B) \\)
```
Lemma sub_image_setI f A B : f @` (A `&` B) `<=` f @` A `&` f @` B.
```

\\( A \subset f^{-1}(A) \\)
```
Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
```
