using System.Diagnostics;
using System.Numerics;
using System.Text;
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
        public static GGRM_GraphDirection None = new(new(0,0), new(0,0), false);
        public static List<GGRM_GraphDirection> allDirections = new List<GGRM_GraphDirection>();

        public bool backwardsTransformation = false;
        public GGRM_N_Subset requirement, transformation;

        public GGRM_GraphDirection(GGRM_N_Subset req, GGRM_N_Subset transform, bool transformBackwards)
        {
            requirement = req;
            transformation = transform;
            backwardsTransformation = transformBackwards;
        }

        public bool IsOpposite(GGRM_GraphDirection potOpposite) //Das mit dem Requirement ist aktuell n bissl unschön, aber naja
        {
            return potOpposite.transformation.a == transformation.a &&
                   potOpposite.transformation.b == transformation.b &&
                   potOpposite.requirement.a == requirement.a &&
                   potOpposite.requirement.b == requirement.b &&
                   backwardsTransformation != potOpposite.backwardsTransformation;
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

        public void GenerateChildren()
        {
            GraphDirection[] tDirList = { GraphDirection.neg3, GraphDirection.neg2, GraphDirection.pos2, GraphDirection.pos3 };

            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                if (subsetTuple.values.a < subsetTuple.originals.a) continue;
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
            newTuple.values = dir.backwardsTransformation ? ((tmp * values - dir.transformation.b) / dir.transformation.a) : (tmp * values * dir.transformation.a + dir.transformation.b);


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
                if (subsetTuple.values.a < subsetTuple.originals.a)
                {
                    bool b = false;
                    foreach (GGRM_GraphNodeSubsetTuple rule in GGRM.allNewRules)
                        if (subsetTuple.originals == rule.originals)
                            b = true;

                    if (!b)
                    {
                        Logger.Log("NEW RULE: " + subsetTuple.originals + "");

                        foundCutoff = true;
                        GGRM.allNewRules.Add(subsetTuple);
                    }
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
            List<GGRM_GraphNodeSubsetTuple> newRootSubsets = new();
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
                var op = incomingDir.backwardsTransformation ? "/" : "*";
                var factor = incomingDir.transformation.a;
                sb.Append($"[{op}{factor}] ");
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

        public GGRM_N_Subset(BigInteger pA, BigInteger pB)
        {
            a = pA; b = pB;
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

    public static class GGRM
    {
        public static void Main(string[] args)
        {
            GGRM_GraphDirection.allDirections.AddRange(new GGRM_GraphDirection[] {
                new GGRM_GraphDirection(new(1, 0), new(2, 0), false),
                new GGRM_GraphDirection(new(2, 0), new(2, 0), true),
                new GGRM_GraphDirection(new(2, 1), new(3, 1), false),
                new GGRM_GraphDirection(new(6, 4), new(3, 1), true)
                });

            Logger.ClearLog();
            const int MAX_DEPTH = 10; //Rekord: 17!

            Stopwatch sw = Stopwatch.StartNew();

            int iteration = 0, furthestDepth = 1;
            cutoffFound = true;

            while (cutoffFound)
            {

                cutoffFound = false;
                for (int i = furthestDepth; i <= MAX_DEPTH; i++)
                {
                    //Logger.Log(i);

                    nodeCount = 0;
                    //GGRM_GraphNodeSubsetTuple.allOriginalLinks.Clear();
                    GGRM_GraphNode beginNode = GGRM_GraphNode.root;

                    if (iteration == 0)
                    {
                        beginNode = GGRM_GraphNode.root = new();
                        beginNode.subsetTuples = new List<GGRM_GraphNodeSubsetTuple>() { new GGRM_GraphNodeSubsetTuple(beginNode, new(1, 0)) };
                    }

                    //if (i == furthestDepth) Logger.Log(beginNode);

                    //foreach (GGRM_GraphNodeSubsetTuple subsetT in beginNode.subsetTuples) Logger.Log(subsetT.originals);
                    //Logger.Log("GRAPHING PROCESS STARTED\n");

                    subsetCount = 0;
                    transpositionCount = 0;
                    GGRM_N_Subset.ModChecks = 0;
                    GGRM_GraphNode.transpositionTable.Clear();
                    RecursiveTreeGeneration(i, beginNode);

                    //Logger.Log("RULE APPLY PROCESS STARTED");
                    foreach (GGRM_GraphNodeSubsetTuple rule in allNewRules) beginNode.ApplyNewRule(rule);
                    allNewRules.Clear();
                    //Logger.Log("RULE APPLY PROCESS ENDED");

                    if (furthestDepth < i) furthestDepth = i;
                    if (cutoffFound || MAX_DEPTH == furthestDepth)
                    {
                        double totalPercentage = 0;
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
                        $"remainingNaturalsSize = {totalPercentage}):");
                        Logger.Log(beginNode);


                        foreach (GGRM_GraphNodeSubsetTuple subsetT in beginNode.subsetTuples) Logger.Log(subsetT.originals);

                        Logger.Log();
                        Logger.Log();
                        Logger.Log();

                        break;
                    }
                }
            }

            sw.Stop();

            Logger.Log($"Elapsed Time: {sw.ElapsedMilliseconds}ms");
        }


        public static bool cutoffFound = true;
        //private static List<GGRM_N_Subset> remainingPossibilities = new();
        private static long nodeCount = 0;
        public static long transpositionCount = 0, subsetCount = 0;
        public static List<GGRM_GraphNodeSubsetTuple> allNewRules = new();

        public static void RecursiveTreeGeneration(int depth, GGRM_GraphNode node)
        {
            nodeCount++;

            if (node == null) return;

            if (node.CheckForLowerCutoffs()) cutoffFound = true;

            if (depth == 0 || cutoffFound) return;

            if (node.CheckForUpperCutoffs(depth)) return;

            node.GenerateChildren();
            foreach (GGRM_GraphNode child in node.childNodes.Values)
                if (!cutoffFound)
                    RecursiveTreeGeneration(depth - 1, child);
        }
    }
}
