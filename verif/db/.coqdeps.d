common/BasicFacts.vo common/BasicFacts.glob common/BasicFacts.v.beautified: common/BasicFacts.v
common/BasicFacts.vio: common/BasicFacts.v
common/lists/ListFacts.vo common/lists/ListFacts.glob common/lists/ListFacts.v.beautified: common/lists/ListFacts.v
common/lists/ListFacts.vio: common/lists/ListFacts.v
common/lists/ListSort.vo common/lists/ListSort.glob common/lists/ListSort.v.beautified: common/lists/ListSort.v common/BasicFacts.vo common/lists/ListFacts.vo common/comparison/OrderedSet.vo common/lists/ListPermut.vo
common/lists/ListSort.vio: common/lists/ListSort.v common/BasicFacts.vio common/lists/ListFacts.vio common/comparison/OrderedSet.vio common/lists/ListPermut.vio
common/lists/ListPermut.vo common/lists/ListPermut.glob common/lists/ListPermut.v.beautified: common/lists/ListPermut.v common/lists/ListFacts.vo common/lists/Mem.vo common/comparison/OrderedSet.vo
common/lists/ListPermut.vio: common/lists/ListPermut.v common/lists/ListFacts.vio common/lists/Mem.vio common/comparison/OrderedSet.vio
common/lists/Mem.vo common/lists/Mem.glob common/lists/Mem.v.beautified: common/lists/Mem.v common/lists/ListFacts.vo
common/lists/Mem.vio: common/lists/Mem.v common/lists/ListFacts.vio
common/lists/Partition.vo common/lists/Partition.glob common/lists/Partition.v.beautified: common/lists/Partition.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/lists/ListSort.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo
common/lists/Partition.vio: common/lists/Partition.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/lists/ListSort.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio
common/comparison/OrderedSet.vo common/comparison/OrderedSet.glob common/comparison/OrderedSet.v.beautified: common/comparison/OrderedSet.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/Mem.vo
common/comparison/OrderedSet.vio: common/comparison/OrderedSet.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/Mem.vio
common/sets/FiniteSetImpl.vo common/sets/FiniteSetImpl.glob common/sets/FiniteSetImpl.v.beautified: common/sets/FiniteSetImpl.v common/comparison/OrderedSet.vo
common/sets/FiniteSetImpl.vio: common/sets/FiniteSetImpl.v common/comparison/OrderedSet.vio
common/sets/FiniteSet.vo common/sets/FiniteSet.glob common/sets/FiniteSet.v.beautified: common/sets/FiniteSet.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/lists/ListSort.vo common/comparison/OrderedSet.vo common/sets/FiniteSetImpl.vo
common/sets/FiniteSet.vio: common/sets/FiniteSet.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/lists/ListSort.vio common/comparison/OrderedSet.vio common/sets/FiniteSetImpl.vio
common/sets/FiniteBag.vo common/sets/FiniteBag.glob common/sets/FiniteBag.v.beautified: common/sets/FiniteBag.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/lists/ListSort.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo
common/sets/FiniteBag.vio: common/sets/FiniteBag.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/lists/ListSort.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio
common/sets/FiniteCollection.vo common/sets/FiniteCollection.glob common/sets/FiniteCollection.v.beautified: common/sets/FiniteCollection.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo
common/sets/FiniteCollection.vio: common/sets/FiniteCollection.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio
common/trees/Tree.vo common/trees/Tree.glob common/trees/Tree.v.beautified: common/trees/Tree.v common/lists/ListFacts.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo
common/trees/Tree.vio: common/trees/Tree.v common/lists/ListFacts.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio
plans/BlockNestedLoop.vo plans/BlockNestedLoop.glob plans/BlockNestedLoop.v.beautified: plans/BlockNestedLoop.v common/comparison/OrderedSet.vo plans/Signatures.vo plans/NestedLoop.vo
plans/BlockNestedLoop.vio: plans/BlockNestedLoop.v common/comparison/OrderedSet.vio plans/Signatures.vio plans/NestedLoop.vio
plans/Filter.vo plans/Filter.glob plans/Filter.v.beautified: plans/Filter.v common/BasicFacts.vo common/lists/ListFacts.vo common/comparison/OrderedSet.vo plans/Signatures.vo
plans/Filter.vio: plans/Filter.v common/BasicFacts.vio common/lists/ListFacts.vio common/comparison/OrderedSet.vio plans/Signatures.vio
plans/IndexJoin.vo plans/IndexJoin.glob plans/IndexJoin.v.beautified: plans/IndexJoin.v common/BasicFacts.vo common/lists/ListFacts.vo common/comparison/OrderedSet.vo plans/Signatures.vo
plans/IndexJoin.vio: plans/IndexJoin.v common/BasicFacts.vio common/lists/ListFacts.vio common/comparison/OrderedSet.vio plans/Signatures.vio
plans/SeqScan.vo plans/SeqScan.glob plans/SeqScan.v.beautified: plans/SeqScan.v common/BasicFacts.vo common/comparison/OrderedSet.vo plans/Signatures.vo
plans/SeqScan.vio: plans/SeqScan.v common/BasicFacts.vio common/comparison/OrderedSet.vio plans/Signatures.vio
plans/Signatures.vo plans/Signatures.glob plans/Signatures.v.beautified: plans/Signatures.v common/BasicFacts.vo common/comparison/OrderedSet.vo
plans/Signatures.vio: plans/Signatures.v common/BasicFacts.vio common/comparison/OrderedSet.vio
plans/BitmapIndexScan.vo plans/BitmapIndexScan.glob plans/BitmapIndexScan.v.beautified: plans/BitmapIndexScan.v common/comparison/OrderedSet.vo plans/Signatures.vo plans/SeqScan.vo
plans/BitmapIndexScan.vio: plans/BitmapIndexScan.v common/comparison/OrderedSet.vio plans/Signatures.vio plans/SeqScan.vio
plans/HashIndexScan.vo plans/HashIndexScan.glob plans/HashIndexScan.v.beautified: plans/HashIndexScan.v common/comparison/OrderedSet.vo common/lists/ListFacts.vo plans/Signatures.vo plans/SeqScan.vo plans/Filter.vo
plans/HashIndexScan.vio: plans/HashIndexScan.v common/comparison/OrderedSet.vio common/lists/ListFacts.vio plans/Signatures.vio plans/SeqScan.vio plans/Filter.vio
plans/NestedLoop.vo plans/NestedLoop.glob plans/NestedLoop.v.beautified: plans/NestedLoop.v common/BasicFacts.vo common/lists/ListFacts.vo common/comparison/OrderedSet.vo plans/Signatures.vo
plans/NestedLoop.vio: plans/NestedLoop.v common/BasicFacts.vio common/lists/ListFacts.vio common/comparison/OrderedSet.vio plans/Signatures.vio
plans/SeqIndexScan.vo plans/SeqIndexScan.glob plans/SeqIndexScan.v.beautified: plans/SeqIndexScan.v common/lists/ListFacts.vo common/comparison/OrderedSet.vo plans/Signatures.vo plans/SeqScan.vo
plans/SeqIndexScan.vio: plans/SeqIndexScan.v common/lists/ListFacts.vio common/comparison/OrderedSet.vio plans/Signatures.vio plans/SeqScan.vio
plans/ThetaNestedLoop.vo plans/ThetaNestedLoop.glob plans/ThetaNestedLoop.v.beautified: plans/ThetaNestedLoop.v common/comparison/OrderedSet.vo plans/Signatures.vo plans/Filter.vo plans/NestedLoop.vo
plans/ThetaNestedLoop.vio: plans/ThetaNestedLoop.v common/comparison/OrderedSet.vio plans/Signatures.vio plans/Filter.vio plans/NestedLoop.vio
plans/Group.vo plans/Group.glob plans/Group.v.beautified: plans/Group.v common/BasicFacts.vo common/comparison/OrderedSet.vo plans/Signatures.vo plans/SeqScan.vo
plans/Group.vio: plans/Group.v common/BasicFacts.vio common/comparison/OrderedSet.vio plans/Signatures.vio plans/SeqScan.vio
plans/QEP.vo plans/QEP.glob plans/QEP.v.beautified: plans/QEP.v common/lists/ListFacts.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo plans/Signatures.vo plans/SeqScan.vo plans/IndexJoin.vo plans/HashIndexScan.vo data/flat/FlatData.vo
plans/QEP.vio: plans/QEP.v common/lists/ListFacts.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio plans/Signatures.vio plans/SeqScan.vio plans/IndexJoin.vio plans/HashIndexScan.vio data/flat/FlatData.vio
plans/Adequacy.vo plans/Adequacy.glob plans/Adequacy.v.beautified: plans/Adequacy.v common/lists/ListFacts.vo common/lists/ListPermut.vo plans/Signatures.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo spec/HighLevelSpec.vo plans/Filter.vo plans/NestedLoop.vo plans/BlockNestedLoop.vo plans/ThetaNestedLoop.vo plans/IndexJoin.vo plans/Group.vo
plans/Adequacy.vio: plans/Adequacy.v common/lists/ListFacts.vio common/lists/ListPermut.vio plans/Signatures.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio spec/HighLevelSpec.vio plans/Filter.vio plans/NestedLoop.vio plans/BlockNestedLoop.vio plans/ThetaNestedLoop.vio plans/IndexJoin.vio plans/Group.vio
data/abstract/Data.vo data/abstract/Data.glob data/abstract/Data.v.beautified: data/abstract/Data.v common/BasicFacts.vo common/lists/ListFacts.vo common/comparison/OrderedSet.vo common/lists/ListPermut.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo
data/abstract/Data.vio: data/abstract/Data.v common/BasicFacts.vio common/lists/ListFacts.vio common/comparison/OrderedSet.vio common/lists/ListPermut.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio
data/flat/FlatData.vo data/flat/FlatData.glob data/flat/FlatData.v.beautified: data/flat/FlatData.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/lists/ListSort.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo common/sets/FiniteCollection.vo common/lists/Partition.vo terms/DExpressions.vo data/abstract/Data.vo
data/flat/FlatData.vio: data/flat/FlatData.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/lists/ListSort.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio common/sets/FiniteCollection.vio common/lists/Partition.vio terms/DExpressions.vio data/abstract/Data.vio
data/sql/SqlCommon.vo data/sql/SqlCommon.glob data/sql/SqlCommon.v.beautified: data/sql/SqlCommon.v common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo common/sets/FiniteCollection.vo common/lists/ListSort.vo common/lists/ListPermut.vo common/lists/Partition.vo terms/DExpressions.vo data/flat/FlatData.vo
data/sql/SqlCommon.vio: data/sql/SqlCommon.v common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio common/sets/FiniteCollection.vio common/lists/ListSort.vio common/lists/ListPermut.vio common/lists/Partition.vio terms/DExpressions.vio data/flat/FlatData.vio
data/sql/SqlAlgebra.vo data/sql/SqlAlgebra.glob data/sql/SqlAlgebra.v.beautified: data/sql/SqlAlgebra.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/lists/ListSort.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo common/sets/FiniteCollection.vo logic/Formula.vo common/lists/Partition.vo terms/DExpressions.vo data/abstract/Data.vo data/flat/FlatData.vo common/trees/Tree.vo data/sql/SqlCommon.vo spec/HighLevelSpec.vo
data/sql/SqlAlgebra.vio: data/sql/SqlAlgebra.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/lists/ListSort.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio common/sets/FiniteCollection.vio logic/Formula.vio common/lists/Partition.vio terms/DExpressions.vio data/abstract/Data.vio data/flat/FlatData.vio common/trees/Tree.vio data/sql/SqlCommon.vio spec/HighLevelSpec.vio
terms/Term.vo terms/Term.glob terms/Term.v.beautified: terms/Term.v common/BasicFacts.vo common/lists/ListFacts.vo common/sets/FiniteSet.vo common/comparison/OrderedSet.vo
terms/Term.vio: terms/Term.v common/BasicFacts.vio common/lists/ListFacts.vio common/sets/FiniteSet.vio common/comparison/OrderedSet.vio
terms/DExpressions.vo terms/DExpressions.glob terms/DExpressions.v.beautified: terms/DExpressions.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListPermut.vo common/lists/ListSort.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo common/sets/FiniteCollection.vo
terms/DExpressions.vio: terms/DExpressions.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListPermut.vio common/lists/ListSort.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio common/sets/FiniteCollection.vio
spec/HighLevelSpec.vo spec/HighLevelSpec.glob spec/HighLevelSpec.v.beautified: spec/HighLevelSpec.v common/comparison/OrderedSet.vo common/sets/FiniteSet.vo
spec/HighLevelSpec.vio: spec/HighLevelSpec.v common/comparison/OrderedSet.vio common/sets/FiniteSet.vio
spec/Bridge.vo spec/Bridge.glob spec/Bridge.v.beautified: spec/Bridge.v common/BasicFacts.vo common/lists/ListFacts.vo common/lists/ListSort.vo common/lists/ListPermut.vo common/comparison/OrderedSet.vo common/sets/FiniteSet.vo common/sets/FiniteBag.vo common/sets/FiniteCollection.vo plans/Signatures.vo plans/SeqScan.vo plans/Filter.vo plans/NestedLoop.vo plans/BlockNestedLoop.vo plans/ThetaNestedLoop.vo plans/IndexJoin.vo plans/Group.vo spec/HighLevelSpec.vo plans/Adequacy.vo common/lists/Partition.vo data/flat/FlatData.vo data/sql/SqlCommon.vo data/sql/SqlAlgebra.vo
spec/Bridge.vio: spec/Bridge.v common/BasicFacts.vio common/lists/ListFacts.vio common/lists/ListSort.vio common/lists/ListPermut.vio common/comparison/OrderedSet.vio common/sets/FiniteSet.vio common/sets/FiniteBag.vio common/sets/FiniteCollection.vio plans/Signatures.vio plans/SeqScan.vio plans/Filter.vio plans/NestedLoop.vio plans/BlockNestedLoop.vio plans/ThetaNestedLoop.vio plans/IndexJoin.vio plans/Group.vio spec/HighLevelSpec.vio plans/Adequacy.vio common/lists/Partition.vio data/flat/FlatData.vio data/sql/SqlCommon.vio data/sql/SqlAlgebra.vio
logic/Formula.vo logic/Formula.glob logic/Formula.v.beautified: logic/Formula.v common/BasicFacts.vo common/lists/ListFacts.vo common/comparison/OrderedSet.vo common/trees/Tree.vo common/sets/FiniteSet.vo common/lists/ListPermut.vo common/lists/ListSort.vo
logic/Formula.vio: logic/Formula.v common/BasicFacts.vio common/lists/ListFacts.vio common/comparison/OrderedSet.vio common/trees/Tree.vio common/sets/FiniteSet.vio common/lists/ListPermut.vio common/lists/ListSort.vio
cursors.vo cursors.glob cursors.v.beautified: cursors.v plans/Signatures.vo ../btrees/btrees.vo
cursors.vio: cursors.v plans/Signatures.vio ../btrees/btrees.vio