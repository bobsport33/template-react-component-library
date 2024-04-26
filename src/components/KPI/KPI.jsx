import React, { useEffect } from "react";

import LinearProgress from "@mui/material/LinearProgress";
import styled from "@emotion/styled";

const KPIWrapper = styled.div`
    width: 100%;
    max-width: 20%;
    height: 100%;
    background-color: var(--neutral100);

    .kpi {
        height: 100%;
        width: 100%;
        &__chart {
            height: 95%;
            width: 95%;
            animation: fadein 5s;
        }
    }
`;

const KPI = ({ id, height, width }) => {
    const app = window.qlikApp;

    const loadVisualization = (id) => {
        if (id === null) {
            return;
        }

        const splitId = id[0].split("|");
        app.visualization.get(splitId[0]).then((vis) => {
            vis.show(id[0]);
        });
    };

    useEffect(() => {
        if (id) {
            loadVisualization(id);
        }
    }, []);

    return (
        <KPIWrapper>
            <div className="kpi">
                <div id={id} className="kpi__chart">
                    <LinearProgress />
                </div>
            </div>
        </KPIWrapper>
    );
};

export default KPI;
