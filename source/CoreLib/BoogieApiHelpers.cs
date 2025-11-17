using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.BaseTypes;
using BType = Microsoft.Boogie.Type;
using Microsoft.Boogie.GraphUtil;
using System.Text.RegularExpressions;

namespace CoreLib
{
    /// <summary>
    /// Helper class to handle Boogie 3.5.5 API changes
    /// </summary>
    public static class BoogieApiHelpers
    {
        /// <summary>
        /// FindBoolAttribute replacement for Boogie 3.5.5
        /// </summary>
        public static bool FindBoolAttribute(QKeyValue kv, string name)
        {
            if (kv == null) return false;

            for (QKeyValue curr = kv; curr != null; curr = curr.Next)
            {
                if (curr.Key == name)
                {
                    if (curr.Params.Count == 0)
                        return true;
                    if (curr.Params.Count == 1 && curr.Params[0] is LiteralExpr lit)
                    {
                        if (lit.isBool && lit.asBool)
                            return true;
                    }
                }
            }
            return false;
        }

        /// <summary>
        /// FindIntAttribute replacement for Boogie 3.5.5
        /// </summary>
        public static int FindIntAttribute(QKeyValue kv, string name, int defaultValue)
        {
            if (kv == null) return defaultValue;

            for (QKeyValue curr = kv; curr != null; curr = curr.Next)
            {
                if (curr.Key == name && curr.Params.Count == 1)
                {
                    if (curr.Params[0] is LiteralExpr lit && lit.isBigNum)
                    {
                        return lit.asBigNum.ToIntSafe;
                    }
                }
            }
            return defaultValue;
        }

        /// <summary>
        /// FindStringAttribute replacement for Boogie 3.5.5
        /// </summary>
        public static string FindStringAttribute(QKeyValue kv, string name)
        {
            if (kv == null) return null;

            for (QKeyValue curr = kv; curr != null; curr = curr.Next)
            {
                if (curr.Key == name && curr.Params.Count == 1)
                {
                    if (curr.Params[0] is LiteralExpr lit && lit.isString)
                    {
                        return lit.Val as string;
                    }
                }
            }
            return null;
        }
        public static bool UserWantsToCheckRoutine(string methodFullname)
        {
            Func<string, bool> match = s => Regex.IsMatch(methodFullname, "^" + Regex.Escape(s).Replace(@"\*", ".*") + "$");
            return (Clo.clo.ProcsToCheck.Count == 0 || Clo.clo.ProcsToCheck.Any(match)) && !Clo.clo.ProcsToIgnore.Any(match);
        }
    }
}

