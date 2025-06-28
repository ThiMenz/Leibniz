using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Numerics;
using System.Reflection.Metadata.Ecma335;
using System.Text;
using System.Transactions;
using System.Windows.Markup;
using System.Xml.Linq;
using CUSTOM_LOGGING;

namespace IDEAS
{
    public class GGRM_GraphNodeSubsetTuple
    {
        public static Dictionary<GGRM_GraphNodeSubsetTuple, List<GGRM_GraphNodeSubsetTuple>> allOriginalLinks = new Dictionary<GGRM_GraphNodeSubsetTuple, List<GGRM_GraphNodeSubsetTuple>>();

        public GGRM_N_Subset originals = new(1, 0), values = new(1, 0);
        public GGRM_GraphNodeSubsetTuple rootTupleRef;
        public GGRM_GraphNode nodeRef;

        public GGRM_GraphNodeSubsetTuple(GGRM_GraphNode node, GGRM_N_Subset pOriginalsAndValues)
        {
            originals = pOriginalsAndValues;
            values = pOriginalsAndValues;
            nodeRef = node;
            rootTupleRef = this;
            allOriginalLinks.Add(this, new());
        }


        public GGRM_GraphNodeSubsetTuple(GGRM_GraphNode node, GGRM_GraphNodeSubsetTuple rootTuple, GGRM_N_Subset pOriginals, GGRM_N_Subset pValues)
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

    public class GGRM_GraphDirection
    {
        public static GGRM_GraphDirection None = new(new(1,0), new(1,0));
        public static List<GGRM_GraphDirection> allDirections = new List<GGRM_GraphDirection>();

        public GGRM_N_Subset requirement, transformation;
        public double sortingIndicator = 0;

        public BigInteger t1, t2, t3, t4;

        public GGRM_GraphDirection(GGRM_N_Subset req, GGRM_N_Subset transform)
        {
            requirement = req;
            transformation = transform;

            BigInteger tggt = BigInteger.GreatestCommonDivisor(requirement.a, transform.a);
            t1 = requirement.b;
            t2 = requirement.a / tggt;
            t3 = transform.a / tggt;
            t4 = transform.b;
            sortingIndicator = (double)t3 / (double)t2;
        }

        public GGRM_N_Subset Transform(GGRM_N_Subset set)
        {
            return (set - t1) / t2 * t3 + t4;
        }

        public static void TryAddNewDirection(GGRM_GraphDirection newDir)
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
            var comparer = Comparer<GGRM_GraphDirection>.Create((x, y) =>
                x.sortingIndicator.CompareTo(y.sortingIndicator)
            );

            // 3) Binary‐search + insert
            int idx = allDirections.BinarySearch(newDir, comparer);
            if (idx < 0) idx = ~idx;
            allDirections.Insert(idx, newDir);
        }


        public bool IsOpposite(GGRM_GraphDirection potOpposite) //Das mit dem Requirement ist aktuell n bissl unschön, aber naja
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
                Logger.Log("No graph directions have been added.");
                return;
            }

            Logger.Log("Index |    Requirement    |    Transformation    ");
            Logger.Log("-------------------------------------------------");

            for (int i = 0; i < allDirections.Count; i++)
            {
                var dir = allDirections[i];
                // assuming GGRM_N_Subset overrides ToString() to something sensible
                Logger.Log(
                    $"{i,5} | {dir.requirement,-17} | {dir.transformation,-19} |{dir.t1}.{dir.t2}.{dir.t3}.{dir.t4}"
                );
            }
        }
    }

    public class GGRM_GraphNode
    {
        public static Dictionary<(BigInteger, BigInteger, BigInteger, BigInteger), bool> transpositionTable = new Dictionary<(BigInteger, BigInteger, BigInteger, BigInteger), bool>();

        public static double staticUncertaintyUntil = 0;
        public static GGRM_GraphNode root;

        public List<GGRM_GraphNodeSubsetTuple> subsetTuples = new();

        public Dictionary<GGRM_GraphDirection, GGRM_GraphNode> childNodes = new();
        public GGRM_GraphNode? parent = null;

        public enum GraphDirection { pos3, pos2, neg2, neg3, none }
        public GGRM_GraphDirection previousGraphDir = GGRM_GraphDirection.None;

        public void GenerateChildren(bool ignoreBelow=true)
        {
            GraphDirection[] tDirList = { GraphDirection.neg3, GraphDirection.neg2, GraphDirection.pos2, GraphDirection.pos3 };

            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                if (ignoreBelow && subsetTuple.values.a < subsetTuple.originals.a) continue;
                foreach (GGRM_GraphDirection dir in GGRM_GraphDirection.allDirections)
                    if (!previousGraphDir.IsOpposite(dir)) AddChild(subsetTuple, dir);
            }
        }

        public void AddChild(GGRM_GraphNodeSubsetTuple subsetTuple, GGRM_GraphDirection dir)
        {
            GGRM_N_Subset values = subsetTuple.values, originals = subsetTuple.originals, tmp;

            bool newDir = !childNodes.ContainsKey(dir);
            GGRM_GraphNode newNode = newDir ? new() : childNodes[dir];
            GGRM_GraphNodeSubsetTuple newTuple = new(newNode, subsetTuple.rootTupleRef, new(1, 0), new(1, 0));

            tmp = (values % dir.requirement.a == dir.requirement.b)[0];

            if (tmp.a == 0) return;

            newTuple.originals = tmp * originals;

            //Logger.Log($"{dir.requirement} ---> {newTuple.originals}");

            //newTuple.values = dir.backwardsTransformation ? ((tmp * values - dir.transformation.b) / dir.transformation.a) : (tmp * values * dir.transformation.a + dir.transformation.b);
            newTuple.values = dir.Transform(tmp * values);

            BigInteger tmpPrevB = newTuple.values.b;
            newTuple.values.b = BigInteger.Abs(newTuple.values.b % newTuple.values.a);
            double tmpDiff = (double)newTuple.values.b - (double)tmpPrevB;

            if (tmpDiff > staticUncertaintyUntil) staticUncertaintyUntil = tmpDiff;

            //Logger.Log(dir.requirement + " | " + tmp + " | " + dir.transformation + "|" + newTuple.values);


            /*switch (dir)
            {
                case GraphDirection.pos3:
                    tmp = (values % 2 == 1)[0];
                    if (tmp.a == 0) return;
                    newTuple.originals = tmp * originals;
                    newTuple.values = tmp * values * 3 + 1;
                    break;
                case GraphDirection.neg3:
                    tmp = (values % 6 == 4)[0];
                    if (tmp.a == 0) return;
                    newTuple.originals = tmp * originals;
                    newTuple.values = (tmp * values - 1) / 3;
                    break;
                case GraphDirection.pos2:
                    newTuple.originals = originals;
                    newTuple.values = values * 2;
                    break;
                case GraphDirection.neg2:
                    tmp = (values % 2 == 0)[0];
                    if (tmp.a == 0) return;
                    newTuple.originals = tmp * originals;
                    newTuple.values = tmp * values / 2;
                    break;
            }*/

            (BigInteger, BigInteger, BigInteger, BigInteger) biArray = (newTuple.values.a, newTuple.values.b, newTuple.originals.a, newTuple.originals.b);
            if (transpositionTable.ContainsKey(biArray))
            {
                GGRM.transpositionCount++;
                //Logger.Log("!!!");
                return;
            }
            transpositionTable.Add(biArray, true);

            GGRM.subsetCount++;
            newNode.parent = this;
            newNode.previousGraphDir = dir;
            newNode.subsetTuples.Add(newTuple);
            if (newDir) childNodes.Add(dir, newNode);
        }

        public bool CheckForUpperCutoffs(int remainingDepth)
        {
            bool b = false;
            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples.ToArray())
            {
                if ((subsetTuple.values.a / subsetTuple.originals.a) > BigInteger.Pow(3, remainingDepth))
                    subsetTuples.Remove(subsetTuple);
            }

            return b;
        }

        public bool CheckForLowerCutoffs()
        {
            bool foundCutoff = false;

            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                BigInteger tmpPrevB = subsetTuple.originals.b;
                while (subsetTuple.originals.b < 0) subsetTuple.originals.b += subsetTuple.originals.a;
                double tmpDiff = (double)subsetTuple.originals.b - (double)tmpPrevB;
                if (tmpDiff > staticUncertaintyUntil) staticUncertaintyUntil = tmpDiff;



                if (subsetTuple.values.a < subsetTuple.originals.a)
                {
                    bool b = false;
                    foreach (GGRM_GraphNodeSubsetTuple rule in GGRM.allNewRules)
                        if (subsetTuple.originals == rule.originals)
                            b = true;

                    if (!b)
                    {
                        if (subsetTuple.originals.a > GGRM.MAX_RULE_A) continue;

                        Logger.Log("NEW RULE: " + subsetTuple.originals + "");
                        //Logger.Log(subsetTuple.rootTupleRef.nodeRef);

                        foundCutoff = true;
                        GGRM.allNewRules.Add(subsetTuple);
                    }
                }
                else
                {
                    // New Dir
                    //Logger.Log(subsetTuple);

                    GGRM.allNewDirections.Add(new(subsetTuple.values, subsetTuple.originals));
                }
            }

            return foundCutoff;
        }

        public void ApplyNewRule(GGRM_GraphNodeSubsetTuple subsetTuple)
        {
            GGRM_N_Subset newRule = subsetTuple.originals;

            List<GGRM_N_Subset> splits = new List<GGRM_N_Subset>();

            double tDiff = (double)(newRule.b - newRule.b % newRule.a);
            if (tDiff > staticUncertaintyUntil) staticUncertaintyUntil = tDiff;

            newRule.b = newRule.b % newRule.a;
            //List<GGRM_GraphNodeSubsetTuple> newRootSubsets = new();
            foreach (GGRM_GraphNodeSubsetTuple rootTuple in root.subsetTuples)
            {
                //Logger.Log("r>" + rootTuple);

                GGRM_N_Subset exception = rootTuple.originals & newRule;

                if (exception.a == 0)
                {
                    splits.Add(rootTuple.originals);
                    continue;
                }

                BigInteger incr = rootTuple.originals.a;
                for (BigInteger i = rootTuple.originals.b; i >= 0; i -= incr) AppendNewRootSubset(splits, rootTuple, new(exception.a, i), newRule);
                for (BigInteger i = rootTuple.originals.b + incr; i < exception.a; i += incr) AppendNewRootSubset(splits, rootTuple, new(exception.a, i), newRule);

                continue;
                for (BigInteger i = 0; i < subsetTuple.originals.a; i++)
                {
                    if (subsetTuple.originals.b == i) continue;

                    GGRM_N_Subset tmpPotNewSubset = new GGRM_N_Subset(subsetTuple.originals.a, i);
                    GGRM_N_Subset t = rootTuple.originals & tmpPotNewSubset;

                    if (t.a != 0)
                    {
                        bool foundEqualOrPartialSubset = false;
                        foreach (GGRM_N_Subset g in splits)
                        {
                            GGRM_N_Subset gANDt = g & t;
                            if (gANDt == g)
                            {
                                foundEqualOrPartialSubset = true;
                                break;
                            }
                            else if (gANDt == t)
                            {
                                splits.Add(t);
                                splits.Remove(g);
                                foundEqualOrPartialSubset = true;
                                break;
                            }
                        }

                        if (!foundEqualOrPartialSubset)
                        {
                            splits.Add(t);
                        }
                    }
                }
            }

            double tStaticUncertainty = (double)(subsetTuple.originals.b - subsetTuple.values.b) / (double)(subsetTuple.values.a - subsetTuple.originals.a);
            if (tStaticUncertainty > staticUncertaintyUntil) staticUncertaintyUntil = tStaticUncertainty;

            GGRM_GraphNodeSubsetTuple.allOriginalLinks.Clear();
            GGRM_GraphNode newRootNode = new();
            root = newRootNode;
            foreach (GGRM_N_Subset subset in splits)
            {
                GGRM_GraphNodeSubsetTuple newBase = new(root, subset);
                //GGRM_GraphNodeSubsetTuple.allOriginalLinks.Add(newBase, new());
                newRootNode.subsetTuples.Add(newBase);
            }
        }

        public void AppendNewRootSubset(List<GGRM_N_Subset> splits, GGRM_GraphNodeSubsetTuple rootTuple, GGRM_N_Subset newSubset, GGRM_N_Subset newRule)
        {
            //Logger.Log(">>" + newSubset);

            if ((newRule & newSubset).a != 0) return;

            GGRM_N_Subset t = rootTuple.originals & newSubset;

            bool foundEqualOrPartialSubset = false;
            /*
            foreach (GGRM_N_Subset g in splits)
            {
                GGRM_N_Subset gANDt = g & t;
                if (gANDt == g)
                {
                    Console.WriteLine("!!!");
                    foundEqualOrPartialSubset = true;
                    break;
                }
                else if (gANDt == t)
                {
                    Console.WriteLine("???");
                    splits.Add(t);
                    splits.Remove(g);
                    foundEqualOrPartialSubset = true;
                    break;
                }
            }*/

            if (!foundEqualOrPartialSubset)
            {
                splits.Add(t);
            }
        }

        #region | TREE STRING CONVERSION |

        public override string ToString()
        {
            var sb = new StringBuilder();
            // start the recursion at the root; we use 'none' so the root itself has no incoming label
            BuildAsciiTree(sb, "", true, GGRM_GraphDirection.None);
            return sb.ToString();
        }

        private void BuildAsciiTree(StringBuilder sb, string indent, bool isLast, GGRM_GraphDirection incomingDir)
        {
            // 1) branch prefix
            sb.Append(indent);
            sb.Append(isLast ? "+- " : "|- ");

            // 2) edge label
            if (incomingDir != GGRM_GraphDirection.None)
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

    public class GGRM_N_Subset
    {
        public BigInteger a, b, mod; //mod is temp
        public double sortingIndicator;

        public GGRM_N_Subset(BigInteger pA, BigInteger pB)
        {
            a = pA; b = pB;
            sortingIndicator = (double)a + ((double)b / (double)a);
        }

        public GGRM_N_Subset(BigInteger pA, BigInteger pB, BigInteger pM)
        {
            a = pA; b = pB; mod = pM;
        }

        public bool Mod(BigInteger modulu, BigInteger result)
        {
            return Mod(this, modulu, result).a != 0; //((a % modulu) + (b % modulu)) % modulu == result;
        }

        public static int ModChecks = 0;
        public static GGRM_N_Subset Mod(GGRM_N_Subset subset, BigInteger m, BigInteger k)
        {
            ModChecks++;
            BigInteger a = subset.a, b = subset.b;
            BigInteger t = k - (b % m) + ((b % m) > k ? 6 : 0);
            if ((a % m) != 0)
                return t % (a % m) == 0 ? new GGRM_N_Subset(m / BigInteger.GreatestCommonDivisor(a, m), t / (a % m)) : new GGRM_N_Subset(0, 0);
            else
                return (a + b) % m == k ? new GGRM_N_Subset(1, 0) : new GGRM_N_Subset(0, 0);
        }
        public static bool operator ==(GGRM_N_Subset subset, GGRM_N_Subset subset2)
        {
            return subset.a == subset2.a && subset.b == subset2.b;
        }
        public static bool operator !=(GGRM_N_Subset subset, GGRM_N_Subset subset2)
        {
            return subset.a != subset2.a || subset.b != subset2.b;
        }
        public static List<GGRM_N_Subset> operator ==(GGRM_N_Subset subset, BigInteger value)
        {
            return new List<GGRM_N_Subset>() { Mod(subset, subset.mod, value) };
        }

        public static List<GGRM_N_Subset> operator !=(GGRM_N_Subset subset, BigInteger value)
        {
            List<GGRM_N_Subset> rList = new List<GGRM_N_Subset>();
            for (BigInteger i = 0; i < subset.mod; i++)
            {
                if (i == value) continue;
                GGRM_N_Subset tSubset = Mod(subset, subset.mod, i);
                if (tSubset.a != 0) rList.Add(Mod(subset, subset.mod, i));
            }
            return rList;
        }

        public static GGRM_N_Subset operator &(GGRM_N_Subset set1, GGRM_N_Subset set2)
        {
            return Mod(set1, set2.a, set2.b) * set1;
        }

        public override bool Equals(object? obj) { return base.Equals(obj); }

        public override int GetHashCode() { return base.GetHashCode(); }

        public override string ToString() { return "{" + a + "n + " + b + "}"; }


        #region | TRIVIAL OPERATORS |

        public static GGRM_N_Subset operator %(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a, subset.b, value); }

        public static GGRM_N_Subset operator +(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a, subset.b + value); }

        public static GGRM_N_Subset operator *(GGRM_N_Subset inner, GGRM_N_Subset outer) { return new GGRM_N_Subset(inner.a * outer.a, inner.b * outer.a + outer.b); }

        public static GGRM_N_Subset operator *(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a * value, subset.b * value); }

        public static GGRM_N_Subset operator -(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a, subset.b - value); }

        public static GGRM_N_Subset operator /(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a / value, subset.b / value); }

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
                allSubsets.Add((idxs, count1 > 0 && count2 > 0));
            }
            return allSubsets;  
        }

        private static bool[] emptyMask = new bool[0];
        public static List<int> GetBeamGraphSubset(bool[] startingPointMask)
        {
            int maxNodeCount = 0, beamGraphNodeIdx = -1;
            for (int i = 0; i < beamGraphNodesGrouped.Length; i++) 
                if (beamGraphNodesGrouped[i].Count > maxNodeCount && !startingPointMask[i]) 
                    (maxNodeCount, beamGraphNodeIdx) = (beamGraphNodesGrouped[i].Count, i);

            if (beamGraphNodeIdx == -1) return new();

            List<int> frontiers = new() { beamGraphNodeIdx };
            //foreach (BeamGraphNode bgn in beamGraphNodesGrouped[beamGraphNodeIdx]) frontiers.Add(bgn);

            //Console.WriteLine(frontiers.Count + " | " + beamGraphNodeIdx);

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
                        //Console.WriteLine(bgn.b1 + "|" + bgn.b2);
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
        public static void CreateRootNode(GGRM_N_Subset singleSubset)
        {
            GGRM_GraphNode.root = new();
            GGRM_GraphNode.root.subsetTuples = new List<GGRM_GraphNodeSubsetTuple>() { new GGRM_GraphNodeSubsetTuple(GGRM_GraphNode.root, singleSubset) };
        }

        public static void ResetTreeStatics()
        {
            allNewDirections.Clear();
            nodeCount = 0;
            subsetCount = 0;
            transpositionCount = 0;
            GGRM_N_Subset.ModChecks = 0;
            GGRM_GraphNode.transpositionTable.Clear();
        }

        public static BigInteger MAX_RULE_A = 400_000;

        public static void Main(string[] args)
        {
            GGRM_GraphDirection[] BeginningArray = { new(new(6, 4), new(2, 1)), new(new(2, 0), new(1, 0)), new(new(1, 0), new(2, 0)), new(new(2, 1), new(6, 4)), };
            foreach (GGRM_GraphDirection dir in BeginningArray) GGRM_GraphDirection.TryAddNewDirection(dir);
            Logger.ClearLog();
            int MAX_DEPTH = 4, DIR_DEPTH = 10; //PB Timeline: 10*1, 16*1, 17*1, 18*1, 3*9, 4*9!
            Stopwatch sw = Stopwatch.StartNew();

            ResetTreeStatics();
            CreateRootNode(new(1, 0));
            RecursiveDualExistance(18, GGRM_GraphNode.root, true);

            BigInteger maxA = 0;
            foreach (GGRM_GraphNodeSubsetTuple tuple in beamCandidates)
            {
                if (tuple.originals.a > maxA) maxA = tuple.originals.a;
                Logger.Log(tuple);

                GGRM_GraphDirection.TryAddNewDirection(new(tuple.originals, new(1, 0)));
                GGRM_GraphDirection.TryAddNewDirection(new(tuple.values, new(1, 0)));
            }

            GGRM_GraphDirection.PrintAllDirections();

            Console.WriteLine("#####################");

            /**************************

            BeamGraphNode.InitBeamGraph((long)maxA);

            Console.WriteLine("#####################");
            int tCount = 0;
            foreach (GGRM_GraphNodeSubsetTuple tuple in beamCandidates)
            {
                BigInteger oA = tuple.originals.a, factor = maxA / oA, tB1 = tuple.originals.b, tB2 = tuple.values.b;
                for (BigInteger i = 0; i < factor; i++)
                {
                    tCount++;
                    //CreateGraphNodes(tB1, tB2);
                    _ = new BeamGraphNode(tB1, tB2);
                    Logger.Log(new GGRM_GraphNodeSubsetTuple(tuple.nodeRef, tuple.rootTupleRef, new(maxA, tB1), new(maxA, tB2)));
                    tB1 += oA; tB2 += oA;
                }
            }
            Console.WriteLine(tCount);

            Console.WriteLine("#####################");

            /*foreach (int i in BeamGraphNode.GetMissingBeamGraphValues()) Console.Write($"{i} ,");
            Console.WriteLine();
            foreach (int i in BeamGraphNode.GetMissingBeamGraphValues()) 
                if (BeamGraphNode.beamGraphNodesGrouped[i].Count != 0) 
                    Console.Write($"{i} ,");

            Console.WriteLine();
            Console.WriteLine(BeamGraphNode.GetMissingBeamGraphValues().Count);*/

            /*
            foreach ((List<int>, bool) subset in BeamGraphNode.GetAllBeamGraphSubsets())
            {
                Console.Write($"ContinousBeam = {subset.Item2}: ");
                foreach (int idx in subset.Item1)
                {
                    Console.Write($"{idx},");
                }
                Console.WriteLine("\n\n");
            }

            //Console.WriteLine(GGRM_GraphNode.root);

            //ResetTreeStatics();
            //CreateRootNode(new(2, 1));
            //CreateRootNode(new(2, 1));
            //RecursiveDualExistance(7, GGRM_GraphNode.root, true);


            ****************************/

            CreateRootNode(new(1, 0));
            ResetTreeStatics();
            //FullRecursiveTreeGeneration(DIR_DEPTH, GGRM_GraphNode.root, true);
            //foreach (GGRM_GraphDirection dir in allNewDirections) GGRM_GraphDirection.TryAddNewDirection(dir);
            //GGRM_GraphDirection.PrintAllDirections();

            //return;

            CreateRootNode(new(1, 0));
            ResetTreeStatics();
            List<GGRM_N_Subset> allRemainingSubsets = new List<GGRM_N_Subset>() { new(1, 0) };
            double previousPercentage = 0.0;

            for (int i = 0; i < 200; i++)
            {
                Logger.Log("-----");
                if (allRemainingSubsets.Count == 0)
                {
                    Logger.Log("================================\n\nIf no programming mistake was made, Collatz Conjecture is proven!\n\n================================");
                    break;
                }
                GGRM_N_Subset selectedSubset = allRemainingSubsets[0];
                allRemainingSubsets.Remove(selectedSubset);
                Logger.Log(selectedSubset + ": \n");
                foreach (GGRM_N_Subset tsubset in ReduceSubset(selectedSubset, MAX_DEPTH))
                {
                    BinaryInsertSubset(allRemainingSubsets, tsubset);
                }
                double totalPercentage = 0;
                SubsetListCompression(allRemainingSubsets);
                foreach (GGRM_N_Subset tsubset in allRemainingSubsets)
                {
                    totalPercentage += 1.0d / (double)tsubset.a;
                    //Logger.Log(tsubset);
                }

                if (previousPercentage == totalPercentage)
                {
                    Logger.Log("DEPTH INCREASE!");
                    MAX_DEPTH++;
                }


                previousPercentage = totalPercentage;
                Logger.Log($"TotalPercentage: " + totalPercentage);
            }

            sw.Stop();

            Logger.Log($"Elapsed Time: {sw.ElapsedMilliseconds}ms");
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

        public static void SubsetListCompression(List<GGRM_N_Subset> list)
        {
            bool changeThisIteration = true;
            while (changeThisIteration) {
                changeThisIteration = false;
                foreach (GGRM_N_Subset subset in list)
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

        private static void BinaryInsertSubset(List<GGRM_N_Subset> list, GGRM_N_Subset subset)
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

                if (midVal < key)
                {
                    // target is to the right
                    low = mid + 1;
                }
                else
                {
                    // midVal >= key, so could be the insertion point
                    high = mid - 1;
                }
            }

            // 'low' is now the index of the first element >= key,
            // or list.Count if all elements were < key.
            list.Insert(low, subset);
        }

        private static bool BinaryRemoveSubsets(List<GGRM_N_Subset> list, BigInteger a, params BigInteger[] bArr)
        {
            double d = (double)a;
            bool allRemoved = true;

            foreach (BigInteger b in bArr)
            {
                double key = d + ((double)b / d);
                if (!BinaryRemoveSubset(list, key))
                {
                    allRemoved = false;
                }
            }

            return allRemoved;
        }

        /// <summary>
        /// Binary‐searches for a subset with exactly this sortingIndicator,
        /// removes it if found, and returns true. Otherwise returns false.
        /// </summary>
        private static bool BinaryRemoveSubset(List<GGRM_N_Subset> list, double key)
        {
            int low = 0;
            int high = list.Count - 1;

            while (low <= high)
            {
                int mid = (low + high) / 2;
                double midVal = list[mid].sortingIndicator;

                if (midVal == key)
                {
                    // found it → remove and return
                    list.RemoveAt(mid);
                    return true;
                }
                else if (midVal < key)
                {
                    low = mid + 1;
                }
                else
                {
                    high = mid - 1;
                }
            }

            // not found
            return false;
        }

        private static bool BinarySearchSubsets(List<GGRM_N_Subset> list, BigInteger a, params BigInteger[] bArr)
        {
            double d = (double)a;
            foreach (BigInteger b in bArr)
            {
                if (!BinarySearchSubset(list, d + ((double)b / d)))
                {
                    return false;
                }
            }
            return true;
        }

        private static bool BinarySearchSubset(List<GGRM_N_Subset> list, double key)
        {
            int low = 0;
            int high = list.Count - 1;

            while (low <= high)
            {
                int mid = (low + high) / 2;
                double midVal = list[mid].sortingIndicator;

                if (midVal == key)
                {
                    return true;
                }
                else if (midVal < key)
                {
                    low = mid + 1;
                }
                else
                {
                    high = mid - 1;
                }
            }

            return false;
        }


        public static List<GGRM_N_Subset> ReduceSubset(GGRM_N_Subset subset, int maxDepth)
        {
            int furthestDepth = 1;
            cutoffFound = false;
            //cutoffFound = true;
            //while (cutoffFound)
            //{
            //    cutoffFound = false;
            //while (furthestDepth != maxDepth)
            //{
            for (int i = furthestDepth; i <= maxDepth; i++) //i = furthest depth
            {
                CreateRootNode(subset);
                GGRM_GraphNode beginNode = GGRM_GraphNode.root;

                //if (i == furthestDepth) Logger.Log(beginNode);
                //foreach (GGRM_GraphNodeSubsetTuple subsetT in beginNode.subsetTuples) Logger.Log(subsetT.originals);
                //Logger.Log("GRAPHING PROCESS STARTED\n");

                ResetTreeStatics();
                RecursiveTreeGeneration(i, beginNode, true);

                foreach (GGRM_GraphNodeSubsetTuple rule in allNewRules) beginNode.ApplyNewRule(rule);
                allNewRules.Clear();

                //foreach (GGRM_GraphDirection dir in allNewDirections) GGRM_GraphDirection.TryAddNewDirection(dir);

                if (furthestDepth < i) furthestDepth = i;
                if (cutoffFound || maxDepth == furthestDepth)
                {
                    //Console.

                    /*double totalPercentage = 0;
                    foreach (GGRM_GraphNodeSubsetTuple subsetT in beginNode.subsetTuples) totalPercentage += (1.0d / (double)subsetT.originals.a);
                    //foreach (GGRM_N_Subset subset in cutoffPossibilities) Logger.Log(subset);
                    Logger.Log();
                    Logger.Log($"{++iteration}. Iteration (depth = {furthestDepth}, " +
                    $"uncertaintyThreshold = {GGRM_GraphNode.staticUncertaintyUntil}, " +
                    $"rootSubsetCount = {beginNode.subsetTuples.Count}, " +
                    $"nodeCount = {nodeCount}, " +
                    $"transposCount = {transpositionCount}, " +
                    $"subsetCount = {subsetCount}, " +
                    $"modChecks = {GGRM_N_Subset.ModChecks}, " +
                    $"dirCount = {GGRM_GraphDirection.allDirections.Count}, " +
                    $"remainingNaturalsSize = {totalPercentage}):");

                    //Logger.Log(beginNode);
                    //GGRM_GraphDirection.PrintAllDirections();

                    foreach (GGRM_GraphNodeSubsetTuple subsetT in beginNode.subsetTuples) Logger.Log(subsetT.originals);

                    Logger.Log();
                    Logger.Log();
                    Logger.Log();*/

                    break;
                }
            //}
            }
            //}
            List<GGRM_N_Subset> rSubsets = new();
            foreach (GGRM_GraphNodeSubsetTuple tsubset in GGRM_GraphNode.root.subsetTuples) rSubsets.Add(tsubset.originals);
            return rSubsets;
        }


        public static bool cutoffFound = true;
        //private static List<GGRM_N_Subset> remainingPossibilities = new();
        private static long nodeCount = 0;
        public static long transpositionCount = 0, subsetCount = 0;
        public static List<GGRM_GraphNodeSubsetTuple> allNewRules = new();
        public static List<GGRM_GraphDirection> allNewDirections = new();

        public static void RecursiveTreeGeneration(int depth, GGRM_GraphNode node, bool isRoot)
        {
            nodeCount++;

            if (node == null) return;

            if (!isRoot && node.CheckForLowerCutoffs()) cutoffFound = true;

            if (depth == 0 || cutoffFound) return;

            //if (node.CheckForUpperCutoffs(depth)) return;

            node.GenerateChildren();
            foreach (GGRM_GraphNode child in node.childNodes.Values)
                if (!cutoffFound)
                    RecursiveTreeGeneration(depth - 1, child, false);
        }

        public static void FullRecursiveTreeGeneration(int depth, GGRM_GraphNode node, bool isRoot)
        {
            nodeCount++;

            if (node == null) return;

            if (!isRoot && node.CheckForLowerCutoffs()) return;

            if (depth == 0) return;

            //if (node.CheckForUpperCutoffs(depth)) return;

            node.GenerateChildren();
            foreach (GGRM_GraphNode child in node.childNodes.Values)
                FullRecursiveTreeGeneration(depth - 1, child, false);
        }

        private static Dictionary<(BigInteger, BigInteger), GGRM_GraphNode> dualExistanceDict = new();

        private static List<GGRM_GraphNodeSubsetTuple> beamCandidates = new();

        private static bool DoesBeamCandidateRepresentationExist(GGRM_GraphNodeSubsetTuple ptuple)
        {
            GGRM_GraphNodeSubsetTuple tuple = new(ptuple.nodeRef, ptuple.rootTupleRef, ptuple.originals, ptuple.values);
            if (tuple.originals.b > tuple.values.b) (tuple.originals.b, tuple.values.b) = (tuple.values.b, tuple.originals.b);

            foreach (GGRM_GraphNodeSubsetTuple iTuple in beamCandidates)
            {
                if (tuple.originals.a < iTuple.originals.a)
                {
                    BigInteger factor = iTuple.originals.a / tuple.originals.a;
                    if (tuple.originals.b * factor == iTuple.originals.b && tuple.values.b * factor == iTuple.values.b)
                    {
                        //Console.WriteLine("=D");
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
                    //Console.WriteLine($">>{tuple}|{iTuple}|{factor}");
                    if (iTuple.originals.b * factor == tuple.originals.b && iTuple.values.b * factor == tuple.values.b)
                    {
                        //Console.WriteLine(":D");
                        return true;
                    }
                }
            }
            beamCandidates.Add(tuple);
            return false;
        }

        private static void RecursiveDualExistance(int depth, GGRM_GraphNode node, bool isRoot) //Ohne Transpostable bisher
        {
            nodeCount++;

            if (node == null) return;

            if (!isRoot && node.subsetTuples[0].values.a == node.subsetTuples[0].originals.a && !DoesBeamCandidateRepresentationExist(node.subsetTuples[0]))
            {
                //GGRM_GraphNode? curNode = node;
                //while (curNode != null)
                //{
                //    if (curNode.subsetTuples.Count == 1) Logger.Log(curNode.subsetTuples[0]);
                //    curNode = curNode.parent;
                //}
                //Logger.Log("!!!" + depth + "\n");
            }

            /*if (isSecond)
            {
                (BigInteger, BigInteger) bTuple = (node.subsetTuples[0].values.a, node.subsetTuples[0].values.b);
                if (dualExistanceDict.ContainsKey(bTuple))
                {
                    Console.WriteLine(node.subsetTuples[0].originals + " <|> " + dualExistanceDict[bTuple].subsetTuples[0].originals);
                    Console.WriteLine(node.subsetTuples[0].values + " <|> " + dualExistanceDict[bTuple].subsetTuples[0].values);
                    GGRM_GraphNode curNode = node;
                    while (curNode != null)
                    {
                        if (curNode.subsetTuples.Count == 1) Console.WriteLine(curNode.subsetTuples[0]);
                        curNode = curNode.parent;
                    } 
                    Console.WriteLine();
                    curNode = dualExistanceDict[bTuple];
                    while (curNode != null)
                    {
                        if (curNode.subsetTuples.Count == 1) Console.WriteLine(curNode.subsetTuples[0]);
                        curNode = curNode.parent;
                    }
                    Console.WriteLine();
                    Console.WriteLine();
                    Console.WriteLine();
                }
            }
            else
            {
                dualExistanceDict.TryAdd((node.subsetTuples[0].values.a, node.subsetTuples[0].values.b), node);
            }*/

            if (depth == 0) return;

            node.GenerateChildren(false);
            foreach (GGRM_GraphNode child in node.childNodes.Values)
                RecursiveDualExistance(depth - 1, child, false);
        }
    }
}
