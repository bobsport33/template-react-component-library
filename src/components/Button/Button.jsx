import React from "react";
import { styled } from "@mui/material";
import PropTypes from "prop-types";

const ButtonWrapper = styled("button")`
    font-size: 5rem;
    background-color: aquamarine;
    border: none;
`;

const Button = ({ backgroundColor, label, onClick }) => {
    return (
        <ButtonWrapper
            style={{ backgroundColor: backgroundColor }}
            onClick={onClick}
        >
            {label}
        </ButtonWrapper>
    );
};

Button.propTypes = {
    backgroundColor: PropTypes.string,
    label: PropTypes.string,
    size: PropTypes.oneOf(["sm", "md", "lg"]),
    onClick: PropTypes.func,
};

export default Button;
