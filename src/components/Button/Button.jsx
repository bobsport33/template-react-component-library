import React from "react";
import { styled } from "@mui/material";
import PropTypes from "prop-types";

const ButtonWrapper = styled("button")`
    padding: 10px 15px;
    border: none;
    font-size: ${({ size }) =>
        size === "lg" ? "2rem" : size === "md" ? "1.5rem " : "1rem"};
`;

const Button = ({ backgroundColor, color, label, size, onClick }) => {
    return (
        <ButtonWrapper
            size={size}
            style={{ backgroundColor: backgroundColor, color: color }}
            onClick={onClick}
        >
            {label}
        </ButtonWrapper>
    );
};

Button.propTypes = {
    backgroundColor: PropTypes.string,
    color: PropTypes.string,
    label: PropTypes.string,
    size: PropTypes.oneOf(["sm", "md", "lg"]),
    onClick: PropTypes.func,
};

export default Button;
