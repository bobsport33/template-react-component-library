import React from "react";
import { styled } from "@mui/material";

const ButtonWrapper = styled("button")`
    font-size: 5rem;
    background-color: aquamarine;
    border: none;
`;

const Button = (props) => {
    return (
        <ButtonWrapper style={{ backgroundColor: props.backgroundColor }}>
            {props.label}
        </ButtonWrapper>
    );
};

export default Button;
