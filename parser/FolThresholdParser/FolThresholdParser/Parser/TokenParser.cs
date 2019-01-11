using System;
using FolThresholdParser.Utils;

namespace FolThresholdParser.Parser
{
    public static class TokenParser
    {
        public static int IndexOfCloseParenthesis(this ArrayView<Token> tokens)
        {
            if (tokens[0].Type != SyntaxKind.OpenParenthesisToken)
                throw new ParserTokenException("Illegal quorum name", tokens[0]);
            var counter = 1;
            for (var index = 1;  index < tokens.Length; ++index)
            {
                if (tokens[index].Type == SyntaxKind.OpenParenthesisToken) ++counter;
                if (tokens[index].Type == SyntaxKind.CloseParenthesisToken) --counter;
                if (counter == 0) return index - 1;
            }

            throw new ParserTokenException("Illegal parenthesis hierarchy", tokens[0]);
        }

        private static int IndexOfFirstSyntaxKindHelper(this ArrayView<Token> tokens, Func<Token, bool> predicate)
        {
            var counter = 0;
            for (var index = 0; index < tokens.Length; ++index)
            {
                if (tokens[index].Type == SyntaxKind.OpenParenthesisToken) ++counter;
                if (tokens[index].Type == SyntaxKind.CloseParenthesisToken) --counter;
                if (counter == 0 && predicate(tokens[index])) return index;
            }

            return -1;
        }

        public static int IndexOfFirstSyntaxKind(this ArrayView<Token> tokens, SyntaxKind kind)
        {
            int res = IndexOfFirstSyntaxKindHelper(tokens, token => token.Type == kind);
            if (res < 0) throw new ParserTokenException($"Missing literal of type {kind}", tokens[0]);
            return res;
        }

        public static int IndexOfFirstSyntaxKindNoThrow(this ArrayView<Token> tokens, SyntaxKind kind)
        {
            return IndexOfFirstSyntaxKindHelper(tokens, token => token.Type == kind);
        }

        public static int IndexOfFirstSyntaxKind(this ArrayView<Token> tokens, SyntaxGeneralType kind)
        {
            int res = IndexOfFirstSyntaxKindHelper(tokens, token => token.GeneralType == kind);
            if (res < 0) throw new ParserTokenException($"Missing literal of type {kind}", tokens[0]);
            return res;
        }

        public static int IndexOfFirstSyntaxKindNoThrow(this ArrayView<Token> tokens, SyntaxGeneralType kind)
        {
            return IndexOfFirstSyntaxKindHelper(tokens, token => token.GeneralType == kind);
        }
    }
}
