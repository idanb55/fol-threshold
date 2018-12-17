using System;
using System.Collections.Generic;

namespace FolThresholdParser
{
    public static class TokenParser
    {
        public static int IndexOfCloseParenthesis(this ArrayView<Token> tokens, int offset)
        {
            if (tokens[offset].Type != SyntaxKind.OpenParenthesisToken)
                throw new Exception($"Expected {SyntaxKind.OpenParenthesisToken}");
            var counter = 1;
            for (var index = offset + 1;  index < tokens.Length; ++index)
            {
                if (tokens[index].Type == SyntaxKind.OpenParenthesisToken) ++counter;
                if (tokens[index].Type == SyntaxKind.CloseParenthesisToken) --counter;
                if (counter == 0) return index - offset - 1;
            }

            throw new Exception("Illegal Parenthesis hierarchy");
        }

        public static int IndexOfFirstSyntaxKind(this ArrayView<Token> tokens, SyntaxGeneralType kind)
        {
            for (var index = 0; index < tokens.Length; ++index)
            {
                if (tokens[index].GeneralType == kind) return index;
            }
            throw new Exception("Could not find element of type");
        }
    }
}
