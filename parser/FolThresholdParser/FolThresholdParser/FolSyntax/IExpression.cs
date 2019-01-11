using System.Collections.Generic;

namespace FolThresholdParser.FolSyntax
{
    public interface IExpression
    {
        IEnumerable<string> VariablesToBind { get; }
    }
}