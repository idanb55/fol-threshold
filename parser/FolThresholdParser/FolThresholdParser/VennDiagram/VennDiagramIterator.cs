using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;

namespace FolThresholdParser.VennDiagram
{
    public static class VennDiagramIterator
    {
        private static IEnumerable<SetExpression> ReadMask(int mask, IReadOnlyList<SetExpression> variables)
        {
            for (var j = 0; j < variables.Count; ++j)
            {
                if ((mask & (1 << j)) == 0)
                {
                    yield return variables[j];
                }
                yield return new SetComplementExpression(variables[j]);
            }
        }

        public static IEnumerable<SetExpression> GetVennZonesHelper(SetVarExpression[] variables)
        {
            for (var i = 0; i < 1 << variables.Length; ++i)
            {
                yield return SetOpExpression.Aggregate(SyntaxKind.AndOperationToken, ReadMask(i, variables.ToArray()).ToArray());
            }
        }
    }
}
