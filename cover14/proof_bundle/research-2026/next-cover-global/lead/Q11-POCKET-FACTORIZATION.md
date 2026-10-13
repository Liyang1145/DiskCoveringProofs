# Exact combinatorial factorization of the q11 locally chorded family

Conditional input: a simple triangulated disk with outer ring0..10 in thatorder, exactly3interior vertices, and everyringchord joinsi−1 toi+1 forsomemiddlelabeli. This is the output proposed in OWNER-COUNT-UNIFICATION.md; this note is purelycombinatorial anddoesnotprove thatinputfromcovers.

LetS be middlelabels of allringchords. In anembeddeddisk, chordsi−1,i+1 andi,i+2 wouldcross foradjacentmiddles, soS independentinC11 andt=|S|≤5. Differentchords cutoff triangular pocketswithdisjointinteriors. Cuttingalongallchords yields:
- onecentral disk withoutercycle consistingof the11−t unremoved ringvertices;
- ttriangular disks withoutervertices(i−1,i,i+1), i∈S.
Thecentralboundaryhas≥6vertices. No piecehas anyringchord left, bydefinition thatallringchordswerecut. Eachof3interiorverticesbelongs to exactlyonepiece. Atriangularpocket with0interiorverticesis itsuniqueall-ringtriangle. A piecewithm>0 hasnoall-ringtriangularface (suchafacecouldonlybe wholeboundarytriangle, leaving noroomforinteriorvertices). Eachcentraltriangulationmusthave≥1interiorvertex: anN≥4disk triangulationwith nointeriorverticesrequiresaringchord.

Consequently centralm is1,2,or3; only≤2interiorvertices lieinallpocketscombined. Possibilities:
1. centralm3: everypocketempty;
2. centralm2: exactlyonepocketcontainsonenode;
3. centralm1: onepocketcontainstwonodes OR twopocketscontainoneeach.
Eachnonemptypieceisa no-chord triangulateddisk oftheprecisetype enumeratedbythehub-skeleton/Euler-walkconstruction, nowwithNcentral∈[6,11],mcentral∈[1,3] andNpocket=3,mpocket∈[1,2]. Theenumerationproof in K10-CATALOGUE-AUDIT.md iscount-independent form≤4 andN≥3; disk link path argumentsapply alsoN3.

Anexhaustiveconstructor therefore loopsindependentS⊂C11; thefourhuballocationtypesabove; labelledno-chordpiecegraphs; andgluesalongthecorrespondingchords. Needalllabelledvariants ofeachpieceorproperstabilizer-orbit quotient—canonicalN-gonpieces CANNOTsimply be gluedatfixedmarkededges without expandingrotations/reflections, sincepocketbaseedgesaredistinguished. FinaldedupusesfullD11×S3 andfacetriangulations, notmerelyedgesunlessfacialembeddingrecoverabilityproved. Keepingoverinclusive labelingsissafe; omittingattachmentorbitsisnot.

Completeness: anyinputdiskhasuniquechordsetS anduniquepiecedecomposition; itslabelledpiecesappearinthepieceenumeration. Gluingtheiractualattachmentsreconstructsit. Soundness: gluingtriangulateddisksalongboundaryedgesinthisnoncrossing patternyieldsatriangulateddiskwiththelistedchords and3interiorvertices. Graph-onlyproofdoesnotensurecoverrealizabilityorcommonwitnessgeometry.

Structuralgain: theunresolvedq11familyneedsnoarbitraryplanar-graphgeneratorandno5Dgrid toclassifytopologically. Itfactorsoverfinitelymanyno-chordpieceswith≤3hubs,andatmosttwooff-corehubnodes. Metricexclusionremainsopen.
