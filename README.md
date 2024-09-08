# argumentation-framework-clustering
GitHub Repository for my Master's Thesis in Computer Science at the University of Technology Graz

## Important Formulas

### Conflict Free Sets
$$ \bigwedge_{a \in A_{SINGLETONS}} \big( \bigwedge_{b:(b,a)\in R, b \in A_{SINGLETONS}} \lnot \big( a \wedge b \big) \big)$$

### Refinement Conflict Free Sets

---
### Admissible Sets
$$ \bigwedge_{a \in A_{SINGLETONS}} \big( \bigwedge_{b:(b,a)\in R, b \in A_{SINGLETONS}} \lnot \big( a \wedge b \big)\big) \land  \bigwedge_{a \in A_{SINGLETONS}} \big( a \rightarrow \bigwedge_{b:(b,a) \in R} \big( \bigvee_{c:(c,b) \in R} c\big) \big)\big)$$


### Refinement Admissible Sets
We refine the formula for the admissible Sets $\varphi_{adm-abs}(\hat F)$ , by adding the refinement $\varphi'(F)$.

$$ \varphi_{adm-abs}(\hat F) \land \varphi'(F) $$


$$\varphi_{adm-abs}(\hat F) = \bigwedge_{\hat a \in \hat A_{SINGLETONS}} \big( \bigwedge_{\hat b:(\hat b,\hat a)\in \hat R, \hat b \in \hat A_{SINGLETONS}} \lnot \big( \hat a \wedge \hat b \big) \land \big( \hat a \rightarrow \bigwedge_{\hat b:(\hat b,\hat a) \in \hat R} \big( \bigvee_{\hat c:(\hat c,\hat b) \in \hat R} \hat c\big) \big)\big)$$


$$\varphi'(F) = \bigwedge_{\hat a \in \hat A_{CLUSTER}} \big( \hat a \rightarrow \bigvee_{a \in \hat a} a \big)  \land \overline{cf}(F) \land \overline{def}(F)$$

$$\overline{cf}(F)=\bigvee_{a \in A_{SINGLETONS}} \big( \bigvee_{b:(b,a)\in R, b \in A_{SINGLETONS}} \big( a \land b \big) \big)$$

$$\overline{def}(F) = \bigvee_{a \in A_{SINGLETONS}}\big( a \land \bigvee_{b:(b,a)\in R} \big( \bigwedge_{c:(c, b)\in R} \lnot c\big)\big)$$

---

### Stable Sets 
$$ \bigwedge_{a \in A_{SINGLETONS}} \big( \bigwedge_{b:(b,a)\in R, b \in A_{SINGLETONS}} \lnot \big( a \wedge b \big) \big) \land \bigwedge_{a \in A} \big( a \bigvee_{b:(b,a)\in R} b\big) \land \bigwedge_{a \in A} \big( \big(  a \bigwedge_{b:(b,a) \in R} \lnot b\big)  \rightarrow \big( \bigwedge_{c:(a,c), c \in A_{SINGLETONS}} \lnot c\big) \big)$$


### Refinement Stable Sets
We refine the formula for the stable Sets $\varphi_{st-abs}(\hat F)$ , by adding the refinement $\varphi'(F)$.

$$ \varphi_{st-abs}(\hat F) \land \varphi'(F) $$

$$\varphi_{st-abs}(\hat F) = \bigwedge_{\hat a \in \hat A_{SINGLETONS}} \big( \bigwedge_{\hat b:(\hat b,\hat a)\in \hat R, \hat b \in \hat A_{SINGLETONS}} \lnot \big( \hat a \wedge \hat b \big) \big) \land \bigwedge_{\hat a \in \hat A} \big( \hat a \bigvee_{\hat b:(\hat b,\hat a)\in \hat R} \hat b\big) \land \bigwedge_{\hat a \in \hat A} \big( \big(  \hat a \bigwedge_{\hat b:(\hat b,\hat a) \in \hat R} \lnot \hat b\big)  \rightarrow \big( \bigwedge_{\hat c:(\hat a,\hat c), \hat c \in \hat A_{SINGLETONS}} \lnot \hat c\big) \big)$$

$$\varphi'(F) = \bigwedge_{\hat a \in \hat A_{CLUSTER}} \big( \hat a \rightarrow \bigvee_{a \in \hat a} a \big)  \land \overline{cf}(F) \land \overline{att}(F) \land \overline{con}(F)$$

$$\overline{cf}(F) = \bigvee_{a \in A_{SINGLETONS}} \big( \bigvee_{b:(b,a)\in R, b \in A_{SINGLETONS}} \big( a \land b \big) \big) $$

$$\overline{att}(F) = \bigvee_{a \in A} \big( \lnot a \bigwedge_{b:(b,a)\in R} \lnot b \big)$$

$$\overline{con}(F) = \bigvee_{a \in A} \big( \big( a \bigwedge_{b:(b,a)\in R} \lnot b) \land \big(\bigvee_{c:(a,c), c\in A_{SINGLETON}} c\big) \big)$$

---

# References and Other Works
[Checking the acceptability of a set of arguments](https://www.researchgate.net/publication/221535800_Checking_the_acceptability_of_a_set_of_arguments)

[Existential Abstraction on Argumentation Frameworks via Clustering](https://proceedings.kr.org/2021/52/kr2021-0052-saribatur-et-al.pdf)

