using System;
using System.Diagnostics;
using System.Numerics;
using System.Text;
using CUSTOM_LOGGING;

namespace IDEAS
{
    public class GraphNodeSubsetTuple
    {
        public static Dictionary<GraphNodeSubsetTuple, List<GraphNodeSubsetTuple>> allOriginalLinks = new Dictionary<GraphNodeSubsetTuple, List<GraphNodeSubsetTuple>>();

        public N_Subset originals = new(1, 0), values = new(1, 0);
        public GraphNodeSubsetTuple rootTupleRef;
        public GraphNode nodeRef;

        public GraphNodeSubsetTuple(GraphNode node, N_Subset pOriginalsAndValues)
        {
            originals = pOriginalsAndValues;
            values = pOriginalsAndValues;
            nodeRef = node;
            rootTupleRef = this;
            allOriginalLinks.Add(this, new());
        }


        public GraphNodeSubsetTuple(GraphNode node, GraphNodeSubsetTuple rootTuple, N_Subset pOriginals, N_Subset pValues)
        {
            originals = pOriginals;
            values = pValues;
            rootTupleRef = rootTuple;
            nodeRef = node;
            allOriginalLinks[rootTupleRef].Add(this);
        }

        public override string ToString()
        {
            return $"({originals}->{values})";
        }

    }

    public class GraphDirection
    {
        public static GraphDirection None = new(new(1,0), new(1,0));
        public static List<GraphDirection> allDirections = new List<GraphDirection>();

        public N_Subset requirement, transformation;
        public double sortingIndicator = 0;

        public BigInteger t1, t2, t3, t4;

        public GraphDirection(N_Subset req, N_Subset transform)
        {
            requirement = req;
            transformation = transform;

            BigInteger tggt = BigInteger.GreatestCommonDivisor(requirement.a, transform.a);
            t1 = requirement.b;
            t2 = requirement.a / tggt;
            t3 = transform.a / tggt;
            t4 = transform.b;
            sortingIndicator = ((double)t3 / (double)t2);
        }

        public N_Subset Transform(N_Subset set)
        {
            return (set - t1) / t2 * t3 + t4;
        }

        public static void TryAddNewDirection(GraphDirection newDir)
        {
            // 0) No‐op if req == transform
            if (newDir.requirement == newDir.transformation)
                return;

            // 1) Dedup check
            foreach (var dir in allDirections)
            {
                var tmpReq = dir.requirement & newDir.requirement;
                //if (newDir.requirement == tmpReq) return;
                if (tmpReq.a != 0 && dir.Transform(newDir.requirement) == newDir.transformation)
                {
                    return;
                }
            }

            // 2) Comparer by sortingIndicator ascending
            var comparer = Comparer<GraphDirection>.Create((x, y) =>
                x.sortingIndicator.CompareTo(y.sortingIndicator)
            );

            // 3) Binary‐search + insert
            int idx = allDirections.BinarySearch(newDir, comparer);
            if (idx < 0) idx = ~idx;
            allDirections.Insert(idx, newDir);
        }


        public bool IsOpposite(GraphDirection potOpposite) //Das mit dem Requirement ist aktuell n bissl unschön, aber naja
        {
            return potOpposite.transformation.a == requirement.a &&
                   potOpposite.transformation.b == requirement.b &&
                   potOpposite.requirement.a == transformation.a &&
                   potOpposite.requirement.b == transformation.b;
        }

        /// <summary>
        /// Prints all directions in the current allDirections list,
        /// in their stored (i.e. sorted-by-transformation.a) order.
        /// </summary>
        public static void PrintAllDirections()
        {
            if (allDirections.Count == 0)
            {
                Logger.WriteLine("No graph directions have been added.");
                return;
            }

            Logger.WriteLine("Index |    Requirement    |    Transformation   | Operation Constants  ");
            Logger.WriteLine("-----------------------------------------------------------------------");

            for (int i = 0; i < allDirections.Count; i++)
            {
                var dir = allDirections[i];
                Logger.WriteLine(
                    $"{i,5} | {dir.requirement,-17} | {dir.transformation,-19} | -{dir.t1}  /{dir.t2}  *{dir.t3}  +{dir.t4}"
                );
            }
        }
    }

    public class GraphNode
    {
        public static Dictionary<(BigInteger, BigInteger, BigInteger, BigInteger), bool> transpositionTable = new Dictionary<(BigInteger, BigInteger, BigInteger, BigInteger), bool>();

        public static double staticUncertaintyUntil = 0;
        public static GraphNode root;

        public List<GraphNodeSubsetTuple> subsetTuples = new();

        public Dictionary<GraphDirection, GraphNode> childNodes = new();
        public GraphNode? parent = null;

        public GraphDirection previousGraphDir = GraphDirection.None;

        public void GenerateChildren(bool ignoreBelow=true)
        {
            foreach (GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                if (ignoreBelow && subsetTuple.values.a < subsetTuple.originals.a) continue;
                foreach (GraphDirection dir in GraphDirection.allDirections)
                    if (!previousGraphDir.IsOpposite(dir)) AddChild(subsetTuple, dir);
            }
        }

        public void AddChild(GraphNodeSubsetTuple subsetTuple, GraphDirection dir)
        {
            N_Subset values = subsetTuple.values, originals = subsetTuple.originals, tmp;

            bool newDir = !childNodes.ContainsKey(dir);
            GraphNode newNode = newDir ? new() : childNodes[dir];
            GraphNodeSubsetTuple newTuple = new(newNode, subsetTuple.rootTupleRef, new(1, 0), new(1, 0));

            tmp = (values % dir.requirement.a == dir.requirement.b)[0];

            if (tmp.a == 0) return;

            newTuple.originals = tmp * originals;

            newTuple.values = dir.Transform(tmp * values);

            BigInteger tmpPrevB = newTuple.values.b;
            newTuple.values.b = BigInteger.Abs(newTuple.values.b % newTuple.values.a);
            double tmpDiff = (double)newTuple.values.b - (double)tmpPrevB;

            if (tmpDiff > staticUncertaintyUntil) staticUncertaintyUntil = tmpDiff;

            (BigInteger, BigInteger, BigInteger, BigInteger) biArray = (newTuple.values.a, newTuple.values.b, newTuple.originals.a, newTuple.originals.b);
            if (transpositionTable.ContainsKey(biArray))
            {
                GGRM.transpositionCount++;
                return;
            }
            transpositionTable.Add(biArray, true);

            GGRM.subsetCount++;
            newNode.parent = this;
            newNode.previousGraphDir = dir;
            newNode.subsetTuples.Add(newTuple);
            if (newDir) childNodes.Add(dir, newNode);
        }

        public bool CheckForLowerCutoffs()
        {
            bool foundCutoff = false;

            foreach (GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                BigInteger tmpPrevB = subsetTuple.originals.b;
                while (subsetTuple.originals.b < 0) subsetTuple.originals.b += subsetTuple.originals.a;
                double tmpDiff = (double)subsetTuple.originals.b - (double)tmpPrevB;
                if (tmpDiff > staticUncertaintyUntil) staticUncertaintyUntil = tmpDiff;



                if (subsetTuple.values.a < subsetTuple.originals.a)
                {
                    bool b = false;
                    foreach (GraphNodeSubsetTuple rule in GGRM.allNewRules)
                        if (subsetTuple.originals == rule.originals)
                            b = true;

                    if (!b)
                    {
                        if (subsetTuple.originals.a > GGRM.MAX_RULE_A) continue;

                        Logger.WriteLine("New Rule: " + subsetTuple.originals + "");
                        foundCutoff = true;
                        GGRM.allNewRules.Add(subsetTuple);
                    }
                }
                else GGRM.allNewDirections.Add(new(subsetTuple.values, subsetTuple.originals));
            }

            return foundCutoff;
        }

        public void ApplyNewRule(GraphNodeSubsetTuple subsetTuple)
        {
            N_Subset newRule = subsetTuple.originals;

            List<N_Subset> splits = new List<N_Subset>();

            double tDiff = (double)(newRule.b - newRule.b % newRule.a);
            if (tDiff > staticUncertaintyUntil) staticUncertaintyUntil = tDiff;

            newRule.b = newRule.b % newRule.a;
            foreach (GraphNodeSubsetTuple rootTuple in root.subsetTuples)
            {
                N_Subset exception = rootTuple.originals & newRule;

                if (exception.a == 0)
                {
                    splits.Add(rootTuple.originals);
                    continue;
                }

                BigInteger incr = rootTuple.originals.a;
                for (BigInteger i = rootTuple.originals.b; i >= 0; i -= incr) AppendNewRootSubset(splits, rootTuple, new(exception.a, i), newRule);
                for (BigInteger i = rootTuple.originals.b + incr; i < exception.a; i += incr) AppendNewRootSubset(splits, rootTuple, new(exception.a, i), newRule);
            }

            double tStaticUncertainty = (double)(subsetTuple.originals.b - subsetTuple.values.b) / (double)(subsetTuple.values.a - subsetTuple.originals.a);
            if (tStaticUncertainty > staticUncertaintyUntil) staticUncertaintyUntil = tStaticUncertainty;

            GraphNodeSubsetTuple.allOriginalLinks.Clear();
            GraphNode newRootNode = new();
            root = newRootNode;
            foreach (N_Subset subset in splits)
            {
                GraphNodeSubsetTuple newBase = new(root, subset);
                newRootNode.subsetTuples.Add(newBase);
            }
        }

        public void AppendNewRootSubset(List<N_Subset> splits, GraphNodeSubsetTuple rootTuple, N_Subset newSubset, N_Subset newRule)
        {
            if ((newRule & newSubset).a != 0) return;

            N_Subset t = rootTuple.originals & newSubset;
            splits.Add(t);
        }

        #region | TREE STRING CONVERSION |

        public override string ToString()
        {
            var sb = new StringBuilder();
            // start the recursion at the root; we use 'none' so the root itself has no incoming label
            BuildAsciiTree(sb, "", true, GraphDirection.None);
            return sb.ToString();
        }

        private void BuildAsciiTree(StringBuilder sb, string indent, bool isLast, GraphDirection incomingDir)
        {
            // 1) branch prefix
            sb.Append(indent);
            sb.Append(isLast ? "+- " : "|- ");

            // 2) edge label
            if (incomingDir != GraphDirection.None)
            {
                // if backwardsTransformation, we’re effectively doing “/a”, else “*a”
                string factor = incomingDir.sortingIndicator.ToString();
                if (factor.Length > 4) factor = factor.Substring(0, 4);
                sb.Append($"[*{factor}] ");
            }

            // 3) list out this node’s subsetTuples via their own ToString()
            if (subsetTuples.Count == 0)
            {
                sb.AppendLine("(no tuples)");
            }
            else
            {
                sb.AppendLine(
                    string.Join(" , ",
                        subsetTuples
                            .Select(t => t.ToString())
                    )
                );
            }

            // 4) compute the next indent
            var childIndent = indent + (isLast ? "   " : "|  ");

            // 5) iterate your dictionary of children
            var entries = childNodes.ToList();
            for (int i = 0; i < entries.Count; i++)
            {
                var dir = entries[i].Key;
                var child = entries[i].Value;

                bool lastChild = (i == entries.Count - 1);
                child.BuildAsciiTree(sb, childIndent, lastChild, dir);
            }
        }


        #endregion
    }

    public class N_Subset
    {
        public BigInteger a, b, mod; //mod is temp
        public double sortingIndicator;

        public N_Subset(BigInteger pA, BigInteger pB)
        {
            a = pA; b = pB;
            sortingIndicator = (double)a + ((double)b / (double)a);
        }

        public N_Subset(BigInteger pA, BigInteger pB, BigInteger pM)
        {
            a = pA; b = pB; mod = pM;
        }

        public bool Mod(BigInteger modulu, BigInteger result)
        {
            return Mod(this, modulu, result).a != 0; //((a % modulu) + (b % modulu)) % modulu == result;
        }

        public static int ModChecks = 0;
        public static N_Subset Mod(N_Subset subset, BigInteger m, BigInteger k)
        {
            ModChecks++;
            BigInteger a = subset.a, b = subset.b;
            BigInteger t = k - (b % m) + ((b % m) > k ? 6 : 0);
            if ((a % m) != 0)
                return t % (a % m) == 0 ? new N_Subset(m / BigInteger.GreatestCommonDivisor(a, m), t / (a % m)) : new N_Subset(0, 0);
            else
                return (a + b) % m == k ? new N_Subset(1, 0) : new N_Subset(0, 0);
        }
        public static bool operator ==(N_Subset subset, N_Subset subset2)
        {
            return subset.a == subset2.a && subset.b == subset2.b;
        }
        public static bool operator !=(N_Subset subset, N_Subset subset2)
        {
            return subset.a != subset2.a || subset.b != subset2.b;
        }
        public static List<N_Subset> operator ==(N_Subset subset, BigInteger value)
        {
            return new List<N_Subset>() { Mod(subset, subset.mod, value) };
        }

        public static List<N_Subset> operator !=(N_Subset subset, BigInteger value)
        {
            List<N_Subset> rList = new List<N_Subset>();
            for (BigInteger i = 0; i < subset.mod; i++)
            {
                if (i == value) continue;
                N_Subset tSubset = Mod(subset, subset.mod, i);
                if (tSubset.a != 0) rList.Add(Mod(subset, subset.mod, i));
            }
            return rList;
        }

        public static N_Subset operator &(N_Subset set1, N_Subset set2)
        {
            return Mod(set1, set2.a, set2.b) * set1;
        }

        public override bool Equals(object? obj) { return base.Equals(obj); }

        public override int GetHashCode() { return base.GetHashCode(); }

        public override string ToString() { return "{" + a + "n + " + b + "}"; }


        #region | TRIVIAL OPERATORS |

        public static N_Subset operator %(N_Subset subset, BigInteger value) { return new N_Subset(subset.a, subset.b, value); }

        public static N_Subset operator +(N_Subset subset, BigInteger value) { return new N_Subset(subset.a, subset.b + value); }

        public static N_Subset operator *(N_Subset inner, N_Subset outer) { return new N_Subset(inner.a * outer.a, inner.b * outer.a + outer.b); }

        public static N_Subset operator *(N_Subset subset, BigInteger value) { return new N_Subset(subset.a * value, subset.b * value); }

        public static N_Subset operator -(N_Subset subset, BigInteger value) { return new N_Subset(subset.a, subset.b - value); }

        public static N_Subset operator /(N_Subset subset, BigInteger value) { return new N_Subset(subset.a / value, subset.b / value); }

        #endregion
    }

    public class BeamGraphNode
    {
        public static List<BeamGraphNode>[] beamGraphNodesGrouped = new List<BeamGraphNode>[0];
        public static List<int>[] beamGraphNodesGroupedIDs = new List<int>[0];
        public static long beamSectionLength = 0;

        public static void InitBeamGraph(long length)
        {
            beamGraphNodesGrouped = new List<BeamGraphNode>[length * 2];
            beamGraphNodesGroupedIDs = new List<int>[length * 2];
            for (int i = 0; i < length * 2; i++)
            {
                beamGraphNodesGrouped[i] = new List<BeamGraphNode>();
                beamGraphNodesGroupedIDs[i] = new List<int>();
            }
            beamSectionLength = length;
        }

        public static List<(List<int>, bool)> GetAllBeamGraphSubsets()
        {
            List<(List<int>, bool)> allSubsets = new();
            bool[] visitedNodes = new bool[beamGraphNodesGrouped.Length];

            bool lastIterationWasEmpty = false; //Not really used
            while (!lastIterationWasEmpty)
            {
                List<int> idxs = GetBeamGraphSubset(visitedNodes);
                if (idxs.Count == 0) break;
                int count1 = 0, count2 = 0;
                foreach (int idx in idxs)
                {
                    visitedNodes[idx] = true;
                    if (idx < beamSectionLength) count1++;
                    else count2++;
                }
                // count1 > 2 && count2 > 2 is not the general criteria; however in this case up until depth 12 nothing fulfills
                // this and everything from depth 12 does so, which is equivalent to the existance of a complete loop
                allSubsets.Add((idxs, count1 > 2 && count2 > 2)); 
            }
            return allSubsets;  
        }

        public static List<int> GetBeamGraphSubset(bool[] startingPointMask)
        {
            int maxNodeCount = 0, beamGraphNodeIdx = -1;
            for (int i = 0; i < beamGraphNodesGrouped.Length; i++) 
                if (beamGraphNodesGrouped[i].Count > maxNodeCount && !startingPointMask[i]) 
                    (maxNodeCount, beamGraphNodeIdx) = (beamGraphNodesGrouped[i].Count, i);

            if (beamGraphNodeIdx == -1) return new();

            List<int> frontiers = new() { beamGraphNodeIdx };

            bool[] visitedNodes = new bool[beamGraphNodesGrouped.Length];
            visitedNodes[beamGraphNodeIdx] = true;

            while (frontiers.Count != 0)
            {
                int[] tempFrontiers = frontiers.ToArray();
                frontiers.Clear();
                foreach (int bgnID in tempFrontiers)
                {
                    foreach (BeamGraphNode bgn in beamGraphNodesGrouped[bgnID])
                    {
                        if (!visitedNodes[(int)bgn.b1])
                        {
                            visitedNodes[(int)bgn.b1] = true;
                            frontiers.Add((int)bgn.b1);
                        }
                        if (!visitedNodes[(int)bgn.b2])
                        {
                            visitedNodes[(int)bgn.b2] = true;
                            frontiers.Add((int)bgn.b2);
                        }
                    }
                }
            }

            List<int> rList = new();
            for (int i = 0; i < beamGraphNodesGrouped.Length; i++)
            {
                if (visitedNodes[i]) rList.Add(i);
            }

            return rList;
        }

        public BeamGraphNode(BigInteger pb1, BigInteger pb2)
        {
            if (pb1 > pb2) (pb1, pb2) = (pb2, pb1);

            b1 = pb1;
            b2 = pb2;

            if (pb2 >= beamSectionLength && pb1 >= beamSectionLength) return;
            else if (pb2 < beamSectionLength)
            {
                beamGraphNodesGrouped[(int)pb1].Add(this);
                beamGraphNodesGrouped[(int)pb2].Add(this);
                BeamGraphNode bgn = new BeamGraphNode(pb1 + beamSectionLength, pb2 + beamSectionLength);
                beamGraphNodesGrouped[(int)pb1 + beamSectionLength].Add(bgn);
                beamGraphNodesGrouped[(int)pb2 + beamSectionLength].Add(bgn);
            }
            else 
            {
                beamGraphNodesGrouped[(int)pb1].Add(this); 
                beamGraphNodesGrouped[(int)pb2].Add(this); 
            }
        }

        public BigInteger b1, b2;

    }

    public static class GGRM
    {
        public static BigInteger MAX_RULE_A = 25_000_000;

        public static void Main(string[] args)
        {
            InitialSetup();

            Stopwatch sw = Stopwatch.StartNew();

            LinearBeamDetection(12); // depth=12 produces the smallest possible continous linear Beam

            MultiDepthDirectionFinder(0); // in case of beam prooving not advantagous, otherwise really efficient (when otherwise high node counts occur)!

            MainReductionLoop(15000, 1);

            sw.Stop();

            Logger.WriteLine($"Elapsed Time: {sw.ElapsedMilliseconds}ms");
        }

        public static void CreateRootNode(N_Subset singleSubset)
        {
            GraphNode.root = new();
            GraphNode.root.subsetTuples = new List<GraphNodeSubsetTuple>() { new GraphNodeSubsetTuple(GraphNode.root, singleSubset) };
        }

        public static void ResetTreeStatics()
        {
            allNewDirections.Clear();
            nodeCount = 0;
            subsetCount = 0;
            transpositionCount = 0;
            N_Subset.ModChecks = 0;
            GraphNode.transpositionTable.Clear();
        }

        public static void InitialSetup()
        {
            GraphDirection[] BeginningArray = { new(new(6, 4), new(2, 1)), new(new(2, 0), new(1, 0)), new(new(1, 0), new(2, 0)), new(new(2, 1), new(6, 4)), };
            foreach (GraphDirection dir in BeginningArray) GraphDirection.TryAddNewDirection(dir);
            Logger.ClearLog();
        }

        public static void LinearBeamDetection(int depth)
        {
            ResetTreeStatics();
            CreateRootNode(new(1, 0));
            Logger.WriteLine("BeamCandidates: ");
            RecursiveDualExistance(depth, GraphNode.root, true);

            BigInteger maxA = 0;
            foreach (GraphNodeSubsetTuple tuple in beamCandidates)
            {
                if (tuple.originals.a > maxA) maxA = tuple.originals.a;
                Logger.WriteLine(tuple);
            }

            BeamGraphNode.InitBeamGraph((long)maxA);

            int tCount = 0;
            foreach (GraphNodeSubsetTuple tuple in beamCandidates)
            {
                BigInteger oA = tuple.originals.a, factor = maxA / oA, tB1 = tuple.originals.b, tB2 = tuple.values.b;
                for (BigInteger i = 0; i < factor; i++)
                {
                    tCount++;
                    _ = new BeamGraphNode(tB1, tB2); 
                    tB1 += oA; tB2 += oA;
                }
            }

            Logger.WriteLine("");

            foreach ((List<int>, bool) subset in BeamGraphNode.GetAllBeamGraphSubsets())
            {
                if (!subset.Item2) continue;

                Logger.Write($"ContinousBeam: ");
                foreach (int idx in subset.Item1)
                {
                    if (GraphNode.staticUncertaintyUntil < idx + (double)maxA) GraphNode.staticUncertaintyUntil = idx + (double)maxA;

                    GraphDirection.TryAddNewDirection(new(new(maxA, idx), new(1, idx)));
                    Logger.Write($"{idx},");
                }
                Logger.WriteLine("\n");
            }

            GraphDirection.PrintAllDirections();

            Logger.WriteLine("");
        }

        public static void MultiDepthDirectionFinder(int dirDepth)
        {
            if (dirDepth == 0) return;
            ResetTreeStatics();
            CreateRootNode(new(1, 0));
            FullRecursiveTreeGeneration(dirDepth, GraphNode.root, true);
            foreach (GraphDirection dir in allNewDirections) GraphDirection.TryAddNewDirection(dir);
            GraphDirection.PrintAllDirections();
            allNewRules.Clear();
        }

        public static void MainReductionLoop(int maxIterations, int initialMaxDepth)
        {
            CreateRootNode(new(1, 0));
            ResetTreeStatics();
            List<N_Subset> allRemainingSubsets = new List<N_Subset>() { new(1, 0) };
            double previousPercentage = 0.0;

            for (int i = 0; i < maxIterations; i++)
            {
                N_Subset selectedSubset = allRemainingSubsets[0];
                allRemainingSubsets.Remove(selectedSubset);
                Logger.WriteLine($"-----\nSelected Subset: {selectedSubset}");
                foreach (N_Subset tsubset in ReduceSubset(selectedSubset, initialMaxDepth)) BinaryInsertSubset(allRemainingSubsets, tsubset);
                double totalPercentage = 0;
                SubsetListCompression(allRemainingSubsets);
                Logger.Write("Current Root Subsets: ");
                foreach (N_Subset tsubset in allRemainingSubsets)
                {
                    totalPercentage += 1.0d / (double)tsubset.a;
                    Logger.Write($"{tsubset}, ");
                }
                Logger.WriteLine("");

                if (previousPercentage == totalPercentage) Logger.WriteLine($"Depth got increased to {++initialMaxDepth}");

                previousPercentage = totalPercentage;
                Logger.WriteLine($"Iteration {i}: percentage={totalPercentage}, nodes={nodeCount}, transpositions={transpositionCount}, staticUncertainty={GraphNode.staticUncertaintyUntil}");

                if (allRemainingSubsets.Count == 0)
                {
                    Logger.WriteLine("\n\n================================\n\nIf no programming mistake was made, Collatz Conjecture has been proven!\n\n================================\n\n");
                    break;
                }
            }
        }

        public static void CreateGraphNodes(BigInteger pB1, BigInteger pB2)
        {
            _ = new BeamGraphNode(pB1, pB2);
            BigInteger t1 = pB1, t2 = pB2;
            while (t1 % 2 == 0 && t2 % 2 == 0) {
                t1 /= 2;
                t2 /= 2; 
                _ = new BeamGraphNode(t1, t2);
            }
            t1 = pB1; t2 = pB2;
            while (t1 < BeamGraphNode.beamSectionLength && t2 < BeamGraphNode.beamSectionLength)
            {
                t1 *= 2;
                t2 *= 2;
                _ = new BeamGraphNode(t1, t2);
            }
        }

        public static void SubsetListCompression(List<N_Subset> list)
        {
            bool changeThisIteration = true;
            while (changeThisIteration) {
                changeThisIteration = false;
                foreach (N_Subset subset in list)
                {
                    if (!subset.a.IsPowerOfTwo)
                    {
                        BigInteger a2 = subset.a / 3;
                        BigInteger b2 = subset.b % a2; //b2, b2 + a2, b2 + 2*a2

                        if (BinarySearchSubsets(list, subset.a, b2, b2 + a2, b2 + 2 * a2))
                        {
                            changeThisIteration = true;
                            BinaryRemoveSubsets(list, subset.a, b2, b2 + a2, b2 + 2 * a2);
                            BinaryInsertSubset(list, new(a2, b2));
                            break;
                        }
                    }

                    if (subset.a % 2 == 0)
                    {
                        BigInteger a2 = subset.a / 2;
                        BigInteger b2 = subset.b % a2; //b2, b2 + a2

                        if (BinarySearchSubsets(list, subset.a, b2, b2 + a2))
                        {
                            changeThisIteration = true;
                            BinaryRemoveSubsets(list, subset.a, b2, b2 + a2);
                            BinaryInsertSubset(list, new(a2, b2));
                            break;
                        }
                    }
                }
            }
        }

        private static void BinaryInsertSubset(List<N_Subset> list, N_Subset subset)
        {
            // If the list is empty, just add and return
            if (list.Count == 0)
            {
                list.Add(subset);
                return;
            }

            int low = 0;
            int high = list.Count - 1;
            double key = subset.sortingIndicator;

            // binary search for the first element >= key
            while (low <= high)
            {
                int mid = (low + high) / 2;
                double midVal = list[mid].sortingIndicator;

                if (midVal < key) low = mid + 1;
                else high = mid - 1;
            }

            // 'low' is now the index of the first element >= key,
            // or list.Count if all elements were < key.
            list.Insert(low, subset);
        }

        private static bool BinaryRemoveSubsets(List<N_Subset> list, BigInteger a, params BigInteger[] bArr)
        {
            double d = (double)a;
            bool allRemoved = true;

            foreach (BigInteger b in bArr)
            {
                double key = d + ((double)b / d);
                if (!BinaryRemoveSubset(list, key)) allRemoved = false;
            }

            return allRemoved;
        }

        /// <summary>
        /// Binary‐searches for a subset with exactly this sortingIndicator,
        /// removes it if found, and returns true. Otherwise returns false.
        /// </summary>
        private static bool BinaryRemoveSubset(List<N_Subset> list, double key)
        {
            int low = 0;
            int high = list.Count - 1;

            while (low <= high)
            {
                int mid = (low + high) / 2;
                double midVal = list[mid].sortingIndicator;

                if (midVal == key) {
                    list.RemoveAt(mid);
                    return true;
                }
                else if (midVal < key) low = mid + 1;
                else high = mid - 1;
            }

            return false;
        }

        private static bool BinarySearchSubsets(List<N_Subset> list, BigInteger a, params BigInteger[] bArr)
        {
            double d = (double)a;
            foreach (BigInteger b in bArr)
                if (!BinarySearchSubset(list, d + ((double)b / d)))
                    return false;
            return true;
        }

        private static bool BinarySearchSubset(List<N_Subset> list, double key)
        {
            int low = 0;
            int high = list.Count - 1;

            while (low <= high)
            {
                int mid = (low + high) / 2;
                double midVal = list[mid].sortingIndicator;

                if (midVal == key) return true;
                else if (midVal < key) low = mid + 1;
                else high = mid - 1;
            }

            return false;
        }


        public static List<N_Subset> ReduceSubset(N_Subset subset, int maxDepth)
        {
            int furthestDepth = 1;
            cutoffFound = false;
            for (int i = furthestDepth; i <= maxDepth; i++)
            {
                CreateRootNode(subset);
                GraphNode beginNode = GraphNode.root;

                ResetTreeStatics();
                RecursiveTreeGeneration(i, beginNode, true);

                foreach (GraphNodeSubsetTuple rule in allNewRules) beginNode.ApplyNewRule(rule);
                allNewRules.Clear();

                if (furthestDepth < i) furthestDepth = i;
                if (cutoffFound || maxDepth == furthestDepth) break;
            }
            List<N_Subset> rSubsets = new();
            foreach (GraphNodeSubsetTuple tsubset in GraphNode.root.subsetTuples) rSubsets.Add(tsubset.originals);
            return rSubsets;
        }


        public static bool cutoffFound = true;
        private static long nodeCount = 0;
        public static long transpositionCount = 0, subsetCount = 0;
        public static List<GraphNodeSubsetTuple> allNewRules = new();
        public static List<GraphDirection> allNewDirections = new();

        public static void RecursiveTreeGeneration(int depth, GraphNode node, bool isRoot)
        {
            nodeCount++;

            if (node == null) return;

            if (!isRoot && node.CheckForLowerCutoffs()) cutoffFound = true;

            if (depth == 0 || cutoffFound) return;

            node.GenerateChildren();
            foreach (GraphNode child in node.childNodes.Values)
                if (!cutoffFound)
                    RecursiveTreeGeneration(depth - 1, child, false);
        }

        public static void FullRecursiveTreeGeneration(int depth, GraphNode node, bool isRoot)
        {
            nodeCount++;

            if (node == null) return;

            if (!isRoot && node.CheckForLowerCutoffs()) return;

            if (depth == 0) return;

            node.GenerateChildren();
            foreach (GraphNode child in node.childNodes.Values)
                FullRecursiveTreeGeneration(depth - 1, child, false);
        }

        private static Dictionary<(BigInteger, BigInteger), GraphNode> dualExistanceDict = new();

        private static List<GraphNodeSubsetTuple> beamCandidates = new();

        private static bool DoesBeamCandidateRepresentationExist(GraphNodeSubsetTuple ptuple)
        {
            GraphNodeSubsetTuple tuple = new(ptuple.nodeRef, ptuple.rootTupleRef, ptuple.originals, ptuple.values);
            if (tuple.originals.b > tuple.values.b) (tuple.originals.b, tuple.values.b) = (tuple.values.b, tuple.originals.b);

            foreach (GraphNodeSubsetTuple iTuple in beamCandidates)
            {
                if (tuple.originals.a < iTuple.originals.a)
                {
                    BigInteger factor = iTuple.originals.a / tuple.originals.a;
                    if (tuple.originals.b * factor == iTuple.originals.b && tuple.values.b * factor == iTuple.values.b)
                    {
                        beamCandidates.Remove(iTuple);
                        break;
                    }
                }
                else if (tuple.originals.a == iTuple.originals.a)
                {
                    if (
                        (tuple.originals.b == iTuple.originals.b && tuple.values.b == iTuple.values.b) ||
                        (tuple.originals.b == iTuple.values.b && tuple.values.b == iTuple.originals.b)
                        ) return true;
                }
                else
                {
                    BigInteger factor = tuple.originals.a / iTuple.originals.a;
                    if (iTuple.originals.b * factor == tuple.originals.b && iTuple.values.b * factor == tuple.values.b) return true;
                }
            }
            beamCandidates.Add(tuple);
            return false;
        }

        private static void RecursiveDualExistance(int depth, GraphNode node, bool isRoot) //Ohne Transpostable bisher
        {
            nodeCount++;

            if (node == null) return;

            if (!isRoot && node.subsetTuples[0].values.a == node.subsetTuples[0].originals.a && !DoesBeamCandidateRepresentationExist(node.subsetTuples[0])) { }

            if (depth == 0) return;

            node.GenerateChildren(false);
            foreach (GraphNode child in node.childNodes.Values)
                RecursiveDualExistance(depth - 1, child, false);
        }
    }
}
