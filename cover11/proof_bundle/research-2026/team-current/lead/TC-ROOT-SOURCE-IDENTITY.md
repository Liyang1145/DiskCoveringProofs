# Source identity of the two TC root models

This is a source-level analytic identity, not inference from pointwise agreement.

Compare tc_s32_kraw.py:121–153 and r20-gluing/r20_tc_iv1.py:symbolic_res5:
1. Both set a4=pi−2(a0+a1+a2+a3) and the identical nine-entry reflected angle list.
2. Both define rho_k=cos(a_k)−sqrt(R²−sin²(a_k)).
3. Both initialize theta4=0 and use precisely the same two recursive sums to define theta0..8.
4. Both define Ck=(rho_k cos(theta_k),rho_k sin(theta_k)) and Uk=Ck+C(k+1)−(cos(theta_k+a_k),sin(theta_k+a_k)). Splitting into Cx,Cy lists changes no function.
5. Both output in the exact order (U1,H1),(U2,H0),(U3,H0),(U8,H1), with residual Euclidean distance minusR.
6. Both use m=(y0+y1)/2, d=(y1−y0)/2, h=sqrt(R²−d²) and fifth residual sqrt((m−Cx6)²+(h−Cy6)²)−R. Historical half=0.5 is the EXACT dyadic rational1/2, not an approximation to a nondyadic constant.
Hence structural induction through assignments proves equality on their common positive-square-root domain. No numerical test or CAS equality oracle is required. SymPy's subsequent identities sin(pi−t)=sin(t), cos(pi−t)=−cos(t) preserve these real functions globally. Exact pi remains part of the original function definition.

Both full12D systems are then defined, from these same five functions f, by F(z,lambda)=(f(z),eR−Df(z)^T lambda), with variable order z=(a0,a1,a2,a3,y0,y1,R). The primary kernel uses nested forward differentiation of the assignment graph; the independent interval tree evaluator uses symbolic derivatives of the same functions. Both enclose the full lambda box in the Hessian block. Thus their interval widths may differ, while their enclosed derivative object is the same.

The independent strict evaluator rejects Float nodes and evaluates rational constants and pi as outward intervals. Its point inverse matrix is only a fixed dyadic preconditioner. The proof is inclusion/contraction on the rational center/radius box, not accuracy or independence of the inverse calculation.
